//! The installation of the generated files of a target in its stage, with
//! the reviewed external declarations of its `models` directory in place of
//! the generated templates, as "Proof targets" in
//! `docs/formal-verification.md` describes it. The installation is that of
//! the CAS project, with the check that every declaration that a reviewed
//! file defines comes from a registered model.

use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::path::Path;

use serde_json::Value;

use super::extract::Extraction;
use super::registry::{Target, declared_axioms};
use super::run::Gate;
use super::{base, lean};

/// Creates the stage `stage` of `target`, from the Lake project of the
/// export, and installs there what `extraction` generated, as [`install`]
/// does with the model registry of the export.
pub fn stage(
    gate: &Gate,
    target: &Target,
    extraction: &Extraction,
    stage: &Path,
) -> Result<Result<Vec<String>, String>, String> {
    let (layout, source, backend) = (gate.layout(), gate.source(), gate.installation()?.backend());
    let pins = source.join(layout.root_project);
    let project = lean::create_stage(&source.join(layout.project), &pins, stage, &backend)?;
    let models = serde_json::from_str(&base::read(&source.join(layout.models))?);
    let models = models.map_err(|error| format!("{}: {error}", layout.models))?;
    install(&source, target, &models, extraction, &project)
}

/// Copies the files that `extraction` generated for `target` into the
/// project `project` of its stage, each template replaced by the reviewed
/// declarations of that name in its `models` directory below `root`, or kept
/// when it has none, and returns the names of the declarations that remain
/// axioms. A reviewed file may only define declarations of its template,
/// each of an item that a model of the model registry `models` provides for
/// the target, and may not use `sorry`; a reviewed file that is missing or
/// does not fit is the inner error, a rejection of the target. A file that
/// cannot be read, other than a missing reviewed file, or written is the
/// outer error, a tool failure.
pub fn install(
    root: &Path,
    target: &Target,
    models: &Value,
    extraction: &Extraction,
    project: &Path,
) -> Result<Result<Vec<String>, String>, String> {
    let failed = |action: &str, path: &Path, error: io::Error| {
        format!("cannot {action} {}: {error}", path.display())
    };
    let (name, mut remaining) = (&target.name, Vec::new());
    for file in extraction.files.keys() {
        let source = extraction.generated.join(file);
        let destination = project.join(file.replace("_Template", ""));
        let parent = destination.parent().unwrap_or(project);
        fs::create_dir_all(parent).map_err(|error| failed("create", parent, error))?;
        let Some(stem) = file.strip_suffix("_Template.lean") else {
            fs::copy(&source, &destination).map_err(|error| failed("copy", &source, error))?;
            continue;
        };
        let kind = stem.rsplit('/').next().unwrap_or(stem);
        let template =
            fs::read_to_string(&source).map_err(|error| failed("read", &source, error))?;
        let text = match &target.models {
            Some(directory) => {
                match fs::read_to_string(root.join(directory).join(format!("{kind}.lean"))) {
                    Ok(text) => text,
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {
                        return Ok(Err(format!("{name}: {directory}/{kind}.lean: {error}")));
                    }
                    Err(error) => return Err(failed("read", &root.join(directory), error)),
                }
            }
            None => template.clone(),
        };
        let generated = BTreeSet::from_iter(declared_axioms(&template));
        let declared = declared_axioms(&text);
        if let Some(axiom) = declared.iter().find(|axiom| !generated.contains(*axiom)) {
            return Ok(Err(format!(
                "{name}: {kind}.lean declares {axiom}, which is not a generated declaration"
            )));
        }
        if text.contains("sorry") {
            return Ok(Err(format!("{name}: {kind}.lean uses sorry")));
        }
        let defined = generated.iter().filter(|axiom| !declared.contains(*axiom));
        if let Some(axiom) = defined
            .into_iter()
            .find(|axiom| !provided(models, name, extraction, axiom))
        {
            return Ok(Err(format!(
                "{name}: {kind}.lean defines {axiom}, which no model of the model registry provides for the target"
            )));
        }
        remaining.extend(declared);
        fs::write(&destination, text).map_err(|error| failed("write", &destination, error))?;
    }
    Ok(Ok(remaining))
}

/// Whether a model of the registry `models` lists the Rust item that the
/// generated declaration `axiom` of `extraction` declares among its `items`
/// and the target `target` among its users.
fn provided(models: &Value, target: &str, extraction: &Extraction, axiom: &str) -> bool {
    let lean = axiom
        .strip_prefix(&format!("{}.", extraction.namespace))
        .unwrap_or(axiom);
    let translation = &extraction.translation;
    let functions = (translation.functions.iter()).map(|item| (&item.lean_name, &item.rust_name));
    let types = (translation.types.iter()).map(|item| (&item.lean_name, &item.rust_name));
    let item = functions
        .chain(types)
        .find(|(name, _)| *name == lean)
        .map(|(_, rust)| rust);
    let listed = |model: &Value| {
        let items = model["items"].as_array().into_iter().flatten();
        items
            .into_iter()
            .any(|listed| item.is_some_and(|item| listed == item.as_str()))
    };
    let models = models["models"].as_array().into_iter().flatten();
    models
        .into_iter()
        .any(|model| listed(model) && model["used_by"].get(target).is_some())
}

#[cfg(test)]
mod tests {
    //! The templates are written as the pinned Aeneas writes them, with the
    //! axioms of their declarations outside the generated namespace.

    use std::collections::BTreeMap;
    use std::os::unix::fs::PermissionsExt;

    use serde_json::json;

    use super::*;
    use crate::formal::extract::{Function, Source, Translation, Type};
    use crate::scratch::Scratch;

    const TEMPLATE: &str = "module\npublic import Aeneas\nopen KrepiGen.M\n\n\
        axiom core.f : Std.U32 → Result Std.U32\n\naxiom core.T : Type\n";

    const NO_MODELS: &str = r#"{"schema": 1, "models": []}"#;

    /// The target `t` of the module `M` with the reviewed declarations of
    /// `models`, if any.
    fn target(models: Option<&str>) -> Target {
        let target = json!({"name": "t", "module": "M", "models": models});
        serde_json::from_value(target).expect("a target")
    }

    /// An extraction of the module `M` in `scratch`, with `Funs.lean` and the
    /// two templates, whose declarations translate `core::f` and `core::T`.
    fn extraction(scratch: &Scratch) -> Extraction {
        let generated = scratch.0.join("aeneas");
        let files = ["Funs", "FunsExternal_Template", "TypesExternal_Template"];
        for file in files {
            let text = if file == "Funs" { "module\n" } else { TEMPLATE };
            scratch.write(&format!("aeneas/KrepiGen/M/{file}.lean"), text);
        }
        let function = Function {
            rust_name: "core::f".to_string(),
            lean_name: "core.f".to_string(),
            lean_file: "KrepiGen/M/FunsExternal_Template.lean".to_string(),
            is_local: false,
            is_opaque: true,
            source: Source {
                file: "/rustc/library/core/src/lib.rs".to_string(),
            },
            loop_info: None,
        };
        let types = vec![Type {
            rust_name: "core::T".to_string(),
            lean_name: "core.T".to_string(),
            lean_file: "KrepiGen/M/TypesExternal_Template.lean".to_string(),
        }];
        Extraction {
            complete: true,
            diagnostics: Vec::new(),
            namespace: "KrepiGen.M".to_string(),
            generated,
            files: BTreeMap::from_iter(
                files.map(|file| (format!("KrepiGen/M/{file}.lean"), String::new())),
            ),
            translation: Translation {
                functions: vec![function],
                types,
            },
        }
    }

    /// Installs the extraction of `scratch` for a target whose reviewed
    /// `FunsExternal.lean` and `TypesExternal.lean` are `text`, with the
    /// model registry `models`, into `project`.
    fn install_reviewed(
        scratch: &Scratch,
        text: &str,
        models: &str,
        project: &str,
    ) -> Result<Result<Vec<String>, String>, String> {
        for kind in ["FunsExternal", "TypesExternal"] {
            scratch.write(&format!("externals/M/{kind}.lean"), text);
        }
        let models: Value = serde_json::from_str(models).expect("a model registry");
        let target = target(Some("externals/M"));
        install(
            &scratch.0,
            &target,
            &models,
            &extraction(scratch),
            &scratch.0.join(project),
        )
    }

    #[test]
    fn the_generated_declarations_are_installed_without_reviewed_ones() {
        let scratch = Scratch::new("externals-generated");
        let models: Value = serde_json::from_str(NO_MODELS).expect("a model registry");
        let project = scratch.0.join("stage/verification");
        let kept = install(
            &scratch.0,
            &target(None),
            &models,
            &extraction(&scratch),
            &project,
        );
        let names = ["core.f", "core.T", "core.f", "core.T"].map(String::from);
        assert_eq!(kept, Ok(Ok(names.to_vec())));
        let read = |file: &str| fs::read_to_string(project.join(file)).expect("an installed file");
        assert_eq!(read("KrepiGen/M/Funs.lean"), "module\n");
        assert_eq!(read("KrepiGen/M/FunsExternal.lean"), TEMPLATE);
        assert!(
            !project
                .join("KrepiGen/M/FunsExternal_Template.lean")
                .exists()
        );
    }

    #[test]
    fn a_reviewed_declaration_that_adds_an_axiom_rejects_the_target() {
        let scratch = Scratch::new("externals-axiom");
        let text = format!("{TEMPLATE}\naxiom cheat : False\n");
        let found = install_reviewed(&scratch, &text, NO_MODELS, "stage");
        let why = "t: FunsExternal.lean declares cheat, which is not a generated declaration";
        assert_eq!(found, Ok(Err(why.to_string())));
    }

    #[test]
    fn a_reviewed_declaration_that_uses_sorry_rejects_the_target() {
        let scratch = Scratch::new("externals-sorry");
        let text = TEMPLATE.replace("axiom core.T : Type", "def core.T : Type := sorry");
        let found = install_reviewed(&scratch, &text, NO_MODELS, "stage");
        assert_eq!(
            found,
            Ok(Err("t: FunsExternal.lean uses sorry".to_string()))
        );
    }

    #[test]
    fn a_definition_that_no_registered_model_provides_rejects_the_target() {
        let scratch = Scratch::new("externals-model");
        let text = TEMPLATE.replace("axiom core.T : Type", "def core.T : Type := Nat");
        let found = install_reviewed(&scratch, &text, NO_MODELS, "stage");
        let why = "t: FunsExternal.lean defines core.T, which no model of the model registry provides for the target";
        assert_eq!(found, Ok(Err(why.to_string())));
        // A model that lists the item for another target provides nothing
        // for this one; one that lists it for this one does.
        let model = |user: &str| {
            let model = json!({"name": "n", "items": ["core::T"], "used_by": {user: []}});
            json!({"schema": 1, "models": [model]}).to_string()
        };
        let found = install_reviewed(&scratch, &text, &model("u"), "other");
        assert_eq!(found, Ok(Err(why.to_string())));
        let found = install_reviewed(&scratch, &text, &model("t"), "provided");
        assert_eq!(
            found,
            Ok(Ok(["core.f", "core.f"].map(String::from).to_vec()))
        );
        // A reviewed file that is missing does not fit the extraction either.
        fs::remove_file(scratch.0.join("externals/M/FunsExternal.lean")).expect("remove a file");
        let models: Value = serde_json::from_str(NO_MODELS).expect("a model registry");
        let target = target(Some("externals/M"));
        let found = install(
            &scratch.0,
            &target,
            &models,
            &extraction(&scratch),
            &scratch.0.join("gone"),
        );
        assert!(
            matches!(&found, Ok(Err(why)) if why.starts_with("t: externals/M/FunsExternal.lean: ")),
            "{found:?}"
        );
    }

    #[test]
    fn a_stage_that_cannot_be_written_is_a_tool_failure() {
        let scratch = Scratch::new("externals-stage");
        // A stage whose directory of generated files cannot be written, and
        // one where a directory stands in place of a reviewed file.
        scratch.write("locked/KrepiGen/M/README", "");
        let locked = scratch.0.join("locked/KrepiGen/M");
        fs::set_permissions(&locked, fs::Permissions::from_mode(0o555)).expect("lock the stage");
        let found = install_reviewed(&scratch, TEMPLATE, NO_MODELS, "locked");
        fs::set_permissions(&locked, fs::Permissions::from_mode(0o755)).expect("unlock the stage");
        assert!(
            matches!(&found, Err(why) if why.starts_with("cannot copy ")),
            "{found:?}"
        );
        fs::create_dir_all(scratch.0.join("taken/KrepiGen/M/FunsExternal.lean"))
            .expect("a directory");
        let found = install_reviewed(&scratch, TEMPLATE, NO_MODELS, "taken");
        assert!(
            matches!(&found, Err(why) if why.starts_with("cannot write ")),
            "{found:?}"
        );
    }
}
