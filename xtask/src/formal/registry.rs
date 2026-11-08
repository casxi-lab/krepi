//! The proof target registry, `verification/targets.json`, as far as the
//! gate reads it: the names of the registered targets and the keys that they
//! prove or leave unclosed, and what the gate does not support yet. Also the
//! names that a Lean file declares with `axiom`, which the generated
//! templates of external items and the reviewed declarations declare.

use std::collections::BTreeSet;

use serde::Deserialize;
use serde::de::IgnoredAny;
use serde_json::Value;

/// The schema version of the registries that this module reads.
pub const SCHEMA: u32 = 1;

/// The fields of the registry that this module reads.
#[derive(Debug, Deserialize)]
struct Registry {
    schema: u32,
    targets: Vec<Target>,
}

#[derive(Debug, Deserialize)]
struct Target {
    name: String,
    proves: Option<Vec<String>>,
    unclosed: Option<Vec<String>>,
    premises: Option<Vec<IgnoredAny>>,
    exclude: Option<Vec<IgnoredAny>>,
}

/// The targets that the registry `text` registers.
fn targets(text: &str) -> Result<Vec<Target>, String> {
    let registry: Registry =
        serde_json::from_str(text).map_err(|error| format!("not a target registry: {error}"))?;
    let schema = registry.schema;
    if schema != SCHEMA {
        return Err(format!("schema {schema} where {SCHEMA} is expected"));
    }
    Ok(registry.targets)
}

/// The names of the targets that the registry `text` registers.
pub fn target_names(text: &str) -> Result<BTreeSet<String>, String> {
    Ok(targets(text)?.into_iter().map(|t| t.name).collect())
}

/// The keys that the targets of `targets` prove or leave unclosed, and what
/// it and the model registry `models` hold that the gate does not support.
pub fn check(targets: &str, models: &str) -> Result<(BTreeSet<String>, Vec<String>), String> {
    let json: Value = serde_json::from_str(models).unwrap_or_default();
    let schema = json["schema"] == SCHEMA;
    let models = json["models"].as_array().filter(|_| schema);
    let models = models.ok_or_else(|| format!("not a model registry of schema {SCHEMA}"))?;
    let model = "models are not compared with their implementations yet".to_string();
    let mut refused = Vec::from_iter((!models.is_empty()).then_some(model));
    let mut keys = BTreeSet::new();
    for target in self::targets(targets)? {
        let name = &target.name;
        if target.premises.is_some_and(|list| !list.is_empty()) {
            refused.push(format!("target {name}: premises are not supported yet"));
        }
        if target.exclude.is_some_and(|list| !list.is_empty()) {
            refused.push(format!("target {name}: exclude is not supported yet"));
        }
        keys.extend(target.proves.into_iter().chain(target.unclosed).flatten());
    }
    Ok((keys, refused))
}

/// Names declared with `axiom` in a Lean file, qualified by the enclosing
/// `namespace` declarations. Aeneas writes a long name on the line after a
/// bare `axiom`. Attributes and declaration modifiers may come before
/// `axiom` on its line.
pub fn declared_axioms(text: &str) -> Vec<String> {
    let mut namespaces: Vec<String> = Vec::new();
    let mut axioms = Vec::new();
    let mut bare = false;
    let qualified = |namespaces: &[String], rest: &str| {
        let end = rest.find(|c: char| c.is_whitespace() || ":{(".contains(c));
        let name = &rest[..end.unwrap_or(rest.len())];
        (namespaces.iter().map(String::as_str))
            .chain([name])
            .collect::<Vec<_>>()
            .join(".")
    };
    for line in text.lines() {
        let trimmed = line.trim_start();
        if bare && !trimmed.is_empty() {
            bare = false;
            axioms.push(qualified(&namespaces, trimmed));
            continue;
        }
        let keyword = (without_modifiers(trimmed).strip_prefix("axiom"))
            .filter(|rest| rest.is_empty() || rest.starts_with(char::is_whitespace));
        if let Some(rest) = keyword {
            match rest.trim() {
                "" => bare = true,
                rest => axioms.push(qualified(&namespaces, rest)),
            }
        } else if let Some(rest) = trimmed.strip_prefix("namespace ") {
            namespaces.push(rest.trim().to_string());
        } else if let Some(name) = trimmed.strip_prefix("end ")
            && namespaces.last().is_some_and(|last| last == name.trim())
        {
            namespaces.pop();
        }
    }
    axioms
}

/// `line` without the attributes, `@[...]`, and the declaration modifiers
/// before its keyword.
fn without_modifiers(mut line: &str) -> &str {
    const MODIFIERS: &str = "public private protected noncomputable unsafe partial";
    loop {
        line = line.trim_start();
        let modifier = MODIFIERS.split(' ').find_map(|modifier| {
            (line.strip_prefix(modifier)).filter(|rest| rest.starts_with(char::is_whitespace))
        });
        if let Some(rest) = modifier {
            line = rest;
        } else if let Some(rest) = line.strip_prefix("@[") {
            // The attribute ends at its closing bracket outside strings.
            let (mut depth, mut quoted) = (1, false);
            let end = rest.char_indices().find_map(|(index, c)| {
                match c {
                    '"' => quoted = !quoted,
                    '[' if !quoted => depth += 1,
                    ']' if !quoted => depth -= 1,
                    _ => {}
                }
                (depth == 0).then_some(index + 1)
            });
            line = end.map_or("", |end| &rest[end..]);
        } else {
            return line;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_names_of_the_registered_targets_are_read() {
        let text = r#"{"schema": 1, "specifications": [],
            "targets": [{"name": "demo", "module": "Demo"}, {"name": "alpha"}]}"#;
        assert_eq!(
            target_names(text),
            Ok(BTreeSet::from(["alpha".to_string(), "demo".to_string()]))
        );
        let committed = include_str!("../../../verification/targets.json");
        assert_eq!(target_names(committed), Ok(BTreeSet::new()));
    }

    #[test]
    fn a_registry_of_another_schema_or_shape_is_refused() {
        assert_eq!(
            target_names(r#"{"schema": 2, "targets": []}"#),
            Err("schema 2 where 1 is expected".to_string())
        );
        let error = target_names(r#"{"schema": 1}"#).expect_err("no targets");
        assert!(error.starts_with("not a target registry: "), "{error}");
        let error = target_names(r#"{"schema": 1, "targets": [{}]}"#).expect_err("no name");
        assert!(error.contains("missing field `name`"), "{error}");
    }

    /// An empty model registry.
    const NO_MODELS: &str = r#"{"schema": 1, "models": []}"#;

    /// The problems of the gate's check for one target `target`.
    fn unsupported(target: &str) -> Vec<String> {
        let targets = format!(r#"{{"schema": 1, "targets": [{target}]}}"#);
        check(&targets, NO_MODELS).expect("valid registries").1
    }

    #[test]
    fn the_keys_of_proves_and_unclosed_are_read() {
        let targets = r#"{"schema": 1, "targets": [
            {"name": "a", "proves": ["kernel/a/src/lib.rs#f"], "unclosed": ["kernel/a/src/lib.rs#g"]},
            {"name": "b", "proves": ["kernel/a/src/lib.rs#f", "kernel/b/src/lib.rs#E::from#2"],
             "premises": [], "exclude": []}]}"#;
        let (keys, unsupported) = check(targets, NO_MODELS).expect("valid registries");
        assert_eq!(
            Vec::from_iter(keys),
            [
                "kernel/a/src/lib.rs#f",
                "kernel/a/src/lib.rs#g",
                "kernel/b/src/lib.rs#E::from#2"
            ]
        );
        assert_eq!(unsupported, Vec::<String>::new());
        for models in [r#"{"schema": 2, "models": []}"#, r#"{"schema": 1}"#, "[]"] {
            let error = check(targets, models).expect_err("not a model registry");
            assert_eq!(error, "not a model registry of schema 1", "{models}");
        }
        let error = check(
            r#"{"schema": 1, "targets": [{"name": "a", "proves": "f"}]}"#,
            NO_MODELS,
        )
        .expect_err("proves is not a list");
        assert!(error.starts_with("not a target registry: "), "{error}");
    }

    #[test]
    fn non_empty_premises_are_refused() {
        assert_eq!(
            unsupported(r#"{"name": "a", "premises": [{}]}"#),
            ["target a: premises are not supported yet"]
        );
    }

    #[test]
    fn a_non_empty_model_registry_is_refused() {
        let models = r#"{"schema": 1, "models": [{"name": "m"}]}"#;
        let (_, unsupported) = check(r#"{"schema": 1, "targets": []}"#, models).expect("valid");
        assert_eq!(
            unsupported,
            ["models are not compared with their implementations yet"]
        );
    }

    #[test]
    fn exclude_cut_points_are_refused() {
        assert_eq!(
            unsupported(r#"{"name": "a", "exclude": ["k::f"]}"#),
            ["target a: exclude is not supported yet"]
        );
        // The committed registries register nothing that the gate refuses.
        let committed = check(
            include_str!("../../../verification/targets.json"),
            include_str!("../../../verification/models.json"),
        );
        assert_eq!(committed, Ok((BTreeSet::new(), Vec::new())));
    }

    #[test]
    fn axioms_are_qualified_by_namespace() {
        let text = "namespace A.B\n@[rust_type \"x\"]\naxiom std.time.Instant : Type\naxiom f {T : Type} : T\nend A.B\naxiom g : Nat\naxiom\n  num.BigInt.Insts.Integer.div_floor\n  : Nat\n";
        assert_eq!(
            declared_axioms(text),
            [
                "A.B.std.time.Instant",
                "A.B.f",
                "g",
                "num.BigInt.Insts.Integer.div_floor"
            ]
        );
    }

    #[test]
    fn axioms_after_attributes_and_modifiers_are_read() {
        let text = "module\n@[expose] public section\nnamespace N\npublic axiom a : False\n\
            private axiom b : False\n@[simp] axiom c : True\n\
            @[rust_fun \"core::slice::{[@T]}::len\"] noncomputable axiom d : Nat\n\
            protected axiom\n  e : Nat\nend N\n@[x] @[y]\taxiom\tf : Nat\n\
            def axiomatic : Nat := 0\n-- axiom g\n";
        assert_eq!(
            declared_axioms(text),
            ["N.a", "N.b", "N.c", "N.d", "N.e", "f"]
        );
    }

    #[test]
    fn the_axioms_of_a_captured_template_are_read() {
        // Templates that the pinned Aeneas wrote, as the tests of the
        // extraction describe them.
        let shared = "fixtures/extraction/shared-pointers/KrepiGen/Qual/SharedPointers";
        let observations = "fixtures/extraction/observations/KrepiGen/Qual/Observations";
        let templates = [
            (
                shared,
                include_str!(
                    "fixtures/extraction/shared-pointers/KrepiGen/Qual/SharedPointers/FunsExternal_Template.lean"
                ),
                &[
                    "alloc.sync.Arc.ptr_eq",
                    "alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref",
                ][..],
            ),
            (
                shared,
                include_str!(
                    "fixtures/extraction/shared-pointers/KrepiGen/Qual/SharedPointers/TypesExternal_Template.lean"
                ),
                &["alloc.sync.Arc"],
            ),
            (
                observations,
                include_str!(
                    "fixtures/extraction/observations/KrepiGen/Qual/Observations/FunsExternal_Template.lean"
                ),
                &["observations.Probe.observe"],
            ),
            (
                observations,
                include_str!(
                    "fixtures/extraction/observations/KrepiGen/Qual/Observations/TypesExternal_Template.lean"
                ),
                &["observations.Probe"],
            ),
        ];
        for (directory, text, axioms) in templates {
            assert_eq!(declared_axioms(text), axioms, "{directory}");
        }
        // The generated definitions declare none.
        let definitions =
            include_str!("fixtures/extraction/observations/KrepiGen/Qual/Observations/Funs.lean");
        assert_eq!(declared_axioms(definitions), Vec::<String>::new());
    }
}
