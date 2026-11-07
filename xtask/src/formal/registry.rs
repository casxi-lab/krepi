//! The proof target registry, `verification/targets.json`, as far as the
//! gate reads it: the names of the registered targets. Also the names that a
//! Lean file declares with `axiom`, which the generated templates of
//! external items and the reviewed declarations that replace them declare.

use std::collections::BTreeSet;

use serde::Deserialize;

/// The schema version of the registry that this module reads.
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
}

/// The names of the targets that the registry `text` registers.
pub fn target_names(text: &str) -> Result<BTreeSet<String>, String> {
    let registry: Registry =
        serde_json::from_str(text).map_err(|error| format!("not a target registry: {error}"))?;
    if registry.schema != SCHEMA {
        return Err(format!(
            "schema {} where {SCHEMA} is expected",
            registry.schema
        ));
    }
    Ok(registry
        .targets
        .into_iter()
        .map(|target| target.name)
        .collect())
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
