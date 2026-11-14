//! The proof target registry, `verification/targets.json`: its targets and
//! specifications, the static rules of the registry that
//! `cargo xtask formal check` applies without running a tool, and what the
//! gate does not support yet. Also the names that a Lean file declares with
//! `axiom`, which the generated templates of external items and the
//! reviewed declarations declare.

use std::collections::{BTreeMap, BTreeSet};

use serde::Deserialize;
use serde_json::Value;

/// The schema version of the target registry.
pub const SCHEMA: u32 = 2;

/// The budget of a target that registers none, in seconds.
pub const BUDGET: u64 = 1_800;

/// The most source mutants that a target may register.
pub const MUTANTS: usize = 30;

/// The registry, `verification/targets.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
#[expect(dead_code, reason = "the schema is read before the registry")]
pub struct Registry {
    pub schema: u32,
    #[serde(default)]
    pub specifications: Vec<Specification>,
    pub targets: Vec<Target>,
}

/// A specification module and the theorems that establish its properties.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
#[expect(dead_code, reason = "the specification phase reads the feature")]
pub struct Specification {
    pub module: String,
    pub feature: Option<String>,
    #[serde(default)]
    pub theorems: Vec<String>,
}

/// Whether a target is registered for the gate or only planned: a planned
/// target is only extracted and type-checked, and needs no obligation and
/// no mutant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Deserialize, serde::Serialize)]
#[serde(rename_all = "lowercase")]
pub enum State {
    #[default]
    Formal,
    Planned,
}

/// A proof target, as "Proof targets" in `docs/formal-verification.md`
/// describes its fields.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Target {
    pub name: String,
    #[serde(default)]
    pub state: State,
    #[serde(default = "budget")]
    pub budget: u64,
    pub module: Option<String>,
    pub feature: Option<String>,
    pub description: Option<String>,
    #[serde(default)]
    pub start_from: Vec<String>,
    #[serde(default)]
    pub opaque: Vec<Opaque>,
    #[serde(default)]
    pub exclude: Vec<Value>,
    pub models: Option<String>,
    #[serde(default)]
    pub unconstrained: Vec<String>,
    #[serde(default)]
    pub proves: Vec<String>,
    #[serde(default)]
    pub unclosed: Vec<String>,
    #[serde(default)]
    pub derived: Vec<String>,
    #[serde(default)]
    pub trusted_axioms: Vec<TrustedAxiom>,
    #[serde(default)]
    pub premises: Vec<Value>,
    #[serde(default)]
    pub proof_modules: Vec<String>,
    #[serde(default)]
    pub obligations: Vec<Obligation>,
    #[serde(default)]
    pub mutants: Vec<Mutant>,
}

fn budget() -> u64 {
    BUDGET
}

/// A cut point: the Charon pattern of the items translated without their
/// bodies, where they are and why the statements do not depend on their
/// bodies.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Opaque {
    pub pattern: String,
    pub source: Option<String>,
    pub reason: Option<String>,
}

/// An axiom beyond the allowlist that the theorems of a target may use.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustedAxiom {
    pub name: String,
    pub reason: String,
}

/// An obligation: a statement and the theorems that establish it.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Obligation {
    pub id: String,
    pub statement: Option<String>,
    #[serde(default)]
    pub theorems: Vec<String>,
}

/// A source mutant: `find`, which occurs once in `file`, replaced by
/// `replace`, must make a theorem of `fails` fail.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Mutant {
    pub name: String,
    pub file: String,
    pub find: String,
    pub replace: String,
    #[serde(default)]
    pub fails: Vec<String>,
}

/// The registry `text` of schema [`SCHEMA`].
pub fn parse(text: &str) -> Result<Registry, String> {
    let not = |error: serde_json::Error| format!("not a target registry: {error}");
    let value: Value = serde_json::from_str(text).map_err(not)?;
    let schema = &value["schema"];
    if schema != SCHEMA {
        return Err(format!("schema {schema} where {SCHEMA} is expected"));
    }
    serde_json::from_value(value).map_err(not)
}

/// The targets that the registry `text` registers, by name, with their
/// states and budgets.
pub fn states(text: &str) -> Result<BTreeMap<String, (State, u64)>, String> {
    let targets = parse(text)?.targets.into_iter();
    Ok(targets
        .map(|target| (target.name, (target.state, target.budget)))
        .collect())
}

/// Whether `text` is empty or only whitespace.
fn blank(text: &Option<String>) -> bool {
    text.as_deref().is_none_or(|text| text.trim().is_empty())
}

/// The static rules of the registry: names, modules and theorems are
/// unique; a target with a module has a root in `start_from`; a formal
/// target has an obligation and a mutant, every obligation a theorem, every
/// mutant a theorem of its target that is to fail; `proves`, `unclosed` and
/// `derived` are disjoint; a cut point gives its source and reason; and no
/// target registers more than [`MUTANTS`] mutants.
pub fn rules(registry: &Registry) -> Vec<String> {
    let mut problems = Vec::new();
    let (mut names, mut modules, mut theorems) =
        (BTreeSet::new(), BTreeMap::new(), BTreeMap::new());
    let mut theorem = |name: &String, place: String, problems: &mut Vec<String>| {
        if let Some(first) = theorems.insert(name.clone(), place.clone()) {
            problems.push(format!(
                "theorem {name} is registered twice: by {first} and by {place}"
            ));
        }
    };
    for specification in &registry.specifications {
        for name in &specification.theorems {
            let place = format!("specification {}", specification.module);
            theorem(name, place, &mut problems);
        }
    }
    for target in &registry.targets {
        let name = &target.name;
        if !names.insert(name) {
            problems.push(format!("two targets are named {name}"));
        }
        if let Some(module) = &target.module
            && let Some(first) = modules.insert(module, name)
        {
            problems.push(format!(
                "target {name}: module {module} is that of target {first} too"
            ));
        }
        if let Some(module) = &target.module
            && target.start_from.is_empty()
        {
            problems.push(format!(
                "target {name}: module {module} has no root in start_from"
            ));
        }
        let formal = target.state == State::Formal;
        if formal && target.obligations.is_empty() {
            problems.push(format!(
                "target {name}: a formal target needs an obligation"
            ));
        }
        let mut own = BTreeSet::new();
        for obligation in &target.obligations {
            let id = &obligation.id;
            if obligation.theorems.is_empty() {
                problems.push(format!("target {name}: obligation {id} has no theorem"));
            }
            for name_of in &obligation.theorems {
                let place = format!("target {name}, obligation {id}");
                theorem(name_of, place, &mut problems);
                own.insert(name_of);
            }
        }
        if formal && target.mutants.is_empty() {
            problems.push(format!("target {name}: a formal target needs a mutant"));
        }
        if target.mutants.len() > MUTANTS {
            let count = target.mutants.len();
            problems.push(format!(
                "target {name}: {count} mutants, more than the {MUTANTS} that a target may register"
            ));
        }
        for mutant in &target.mutants {
            let mutant_name = &mutant.name;
            if mutant.fails.is_empty() {
                problems.push(format!(
                    "target {name}: mutant {mutant_name} names no theorem to fail"
                ));
            }
            for fails in mutant.fails.iter().filter(|fails| !own.contains(fails)) {
                problems.push(format!(
                    "target {name}: mutant {mutant_name} names {fails}, which is no theorem of the target's obligations"
                ));
            }
        }
        let lists = [
            ("proves", &target.proves),
            ("unclosed", &target.unclosed),
            ("derived", &target.derived),
        ];
        for (index, (first, keys)) in lists.iter().enumerate() {
            for (second, others) in &lists[index + 1..] {
                for key in keys.iter().filter(|key| others.contains(key)) {
                    problems.push(format!(
                        "target {name}: {key} is in {first} and in {second}"
                    ));
                }
            }
        }
        for opaque in &target.opaque {
            let pattern = &opaque.pattern;
            for (field, text) in [("source", &opaque.source), ("reason", &opaque.reason)] {
                if blank(text) {
                    problems.push(format!("target {name}: opaque {pattern} has no {field}"));
                }
            }
        }
    }
    problems
}

/// `verification/axioms.json`, with the fields that the gate requires, as
/// `lean::load_axioms` reads it, and refuses a field that it does not know;
/// the source and the reason are optional here, so that the rule reports
/// each axiom that lacks one.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Axioms {
    schema: u32,
    axioms: Vec<LibraryAxiom>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct LibraryAxiom {
    name: String,
    source: Option<String>,
    reason: Option<String>,
}

/// The static rule of the registry of library axioms `text`: every axiom
/// gives its source and reason. An empty text or one of only whitespace
/// gives neither.
pub fn axiom_rules(text: &str) -> Result<Vec<String>, String> {
    let axioms: Axioms = serde_json::from_str(text)
        .map_err(|error| format!("not a registry of library axioms: {error}"))?;
    if axioms.schema != 1 {
        return Err(format!("schema {} where 1 is expected", axioms.schema));
    }
    let mut problems = Vec::new();
    for axiom in &axioms.axioms {
        let name = &axiom.name;
        for (field, text) in [("source", &axiom.source), ("reason", &axiom.reason)] {
            if blank(text) {
                problems.push(format!("axiom {name} has no {field}"));
            }
        }
    }
    Ok(problems)
}

/// The registry `targets`, and the problems of it and of the model
/// registry `models`: the static rules, the shard limit ([`super::merge`])
/// and what the gate does not support yet.
pub fn check(targets: &str, models: &str) -> Result<(Registry, Vec<String>), String> {
    let json: Value = serde_json::from_str(models).unwrap_or_default();
    let schema = json["schema"] == 1;
    let models = json["models"].as_array().filter(|_| schema);
    let models = models.ok_or_else(|| "not a model registry of schema 1".to_string())?;
    let model = "models are not compared with their implementations yet".to_string();
    let mut problems = Vec::from_iter((!models.is_empty()).then_some(model));
    let registry = parse(targets)?;
    for target in &registry.targets {
        let name = &target.name;
        if !target.premises.is_empty() {
            problems.push(format!("target {name}: premises are not supported yet"));
        }
        if !target.exclude.is_empty() {
            problems.push(format!("target {name}: exclude is not supported yet"));
        }
    }
    problems.extend(super::merge::budget_problems(&registry.targets));
    problems.extend(rules(&registry));
    Ok((registry, problems))
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
pub(crate) mod tests {
    use serde_json::json;

    use super::*;

    /// A registry that keeps every rule: a formal target and a planned one
    /// without obligations and mutants, beside a specification.
    pub(crate) fn valid() -> Value {
        json!({
            "schema": 2,
            "specifications": [{
                "module": "Krepi.Spec.Table",
                "feature": "krepi.memory.table",
                "theorems": ["Krepi.Spec.Table.lookup_total"]
            }],
            "targets": [
                {
                    "name": "table",
                    "module": "Table",
                    "feature": "krepi.memory.table",
                    "description": "The lookup of the table.",
                    "budget": 900,
                    "start_from": ["krepi_kernel::table::lookup"],
                    "opaque": [{
                        "pattern": "krepi_kernel::table::hardware::read",
                        "source": "kernel/src/table.rs",
                        "reason": "A register read, a deterministic function of its arguments: no statement depends on two reads agreeing."
                    }],
                    "unconstrained": [],
                    "proves": ["kernel/src/table.rs#lookup"],
                    "unclosed": ["kernel/src/table.rs#hardware::read"],
                    "derived": ["kernel/src/table.rs#Slot::clone"],
                    "proof_modules": ["Krepi.Proofs.Table"],
                    "obligations": [{
                        "id": "lookup",
                        "statement": "Krepi.Statements.Table.lookup",
                        "theorems": ["Krepi.Proofs.Table.lookup_refines", "Krepi.Proofs.Table.lookup_bound"]
                    }],
                    "mutants": [{
                        "name": "bound",
                        "file": "kernel/src/table.rs",
                        "find": "index < 4",
                        "replace": "index <= 4",
                        "fails": ["Krepi.Proofs.Table.lookup_bound"]
                    }]
                },
                {
                    "name": "slots",
                    "state": "planned",
                    "module": "Slots",
                    "start_from": ["krepi_kernel::slots"]
                }
            ]
        })
    }

    /// The problems of the static rules on [`valid`] after `edit`.
    fn broken(edit: impl FnOnce(&mut Value)) -> Vec<String> {
        let mut registry = valid();
        edit(&mut registry);
        rules(&parse(&registry.to_string()).expect("a registry"))
    }

    /// The formal target of [`valid`] in `registry`.
    fn table(registry: &mut Value) -> &mut Value {
        &mut registry["targets"][0]
    }

    #[test]
    fn the_targets_are_read_with_their_states_and_budgets() {
        let registry = parse(&valid().to_string()).expect("a registry");
        let read: Vec<_> = (registry.targets.iter())
            .map(|target| (target.name.as_str(), target.state, target.budget))
            .collect();
        assert_eq!(
            read,
            [
                ("table", State::Formal, 900),
                ("slots", State::Planned, BUDGET)
            ]
        );
        assert_eq!(
            states(&valid().to_string()),
            Ok(BTreeMap::from([
                ("slots".to_string(), (State::Planned, BUDGET)),
                ("table".to_string(), (State::Formal, 900))
            ]))
        );
        let committed = include_str!("../../../verification/targets.json");
        assert_eq!(states(committed), Ok(BTreeMap::new()));
        let committed = parse(committed).expect("the committed registry");
        assert_eq!(rules(&committed), Vec::<String>::new());
    }

    #[test]
    fn the_rules_hold_on_a_registry_that_keeps_them() {
        // The planned target has neither an obligation nor a mutant.
        assert_eq!(broken(|_| ()), Vec::<String>::new());
    }

    #[test]
    fn a_registry_of_another_schema_or_shape_is_refused() {
        assert_eq!(
            states(r#"{"schema": 1, "targets": []}"#),
            Err("schema 1 where 2 is expected".to_string())
        );
        assert_eq!(
            states(r#"{"targets": []}"#),
            Err("schema null where 2 is expected".to_string())
        );
        for (text, error) in [
            (r#"{"schema": 2}"#, "missing field `targets`"),
            (r#"{"schema": 2, "targets": [{}]}"#, "missing field `name`"),
            (
                r#"{"schema": 2, "targets": [{"name": "a", "state": "proved"}]}"#,
                "unknown variant `proved`",
            ),
            (
                r#"{"schema": 2, "targets": [{"name": "a", "opaque": ["k::f"]}]}"#,
                "invalid type: string",
            ),
            (
                r#"{"schema": 2, "targets": [{"name": "a", "mutant": []}]}"#,
                "unknown field `mutant`",
            ),
            (
                r#"{"schema": 2, "targets": [{"name": "a", "proves": "f"}]}"#,
                "invalid type: string",
            ),
        ] {
            let found = states(text).expect_err("not a registry");
            assert!(
                found.starts_with("not a target registry: ") && found.contains(error),
                "{text}: {found}"
            );
        }
    }

    #[test]
    fn two_targets_of_one_name_fail() {
        let problems = broken(|registry| registry["targets"][1]["name"] = json!("table"));
        assert_eq!(problems, ["two targets are named table"]);
    }

    #[test]
    fn two_targets_of_one_module_fail() {
        let problems = broken(|registry| registry["targets"][1]["module"] = json!("Table"));
        assert_eq!(
            problems,
            ["target slots: module Table is that of target table too"]
        );
    }

    #[test]
    fn a_target_with_a_module_and_no_root_fails() {
        let problems = broken(|registry| table(registry)["start_from"] = json!([]));
        assert_eq!(
            problems,
            ["target table: module Table has no root in start_from"]
        );
        let problems = broken(|registry| registry["targets"][1]["start_from"] = json!([]));
        assert_eq!(
            problems,
            ["target slots: module Slots has no root in start_from"]
        );
        // A target without a module needs no root.
        let problems = broken(|registry| {
            let slots = registry["targets"][1].as_object_mut().expect("a target");
            slots.remove("module");
            slots.remove("start_from");
        });
        assert_eq!(problems, Vec::<String>::new());
    }

    #[test]
    fn a_theorem_registered_twice_fails() {
        // Twice in one obligation, in two targets and in a specification.
        let repeated = broken(|registry| {
            let theorems = &mut table(registry)["obligations"][0]["theorems"];
            let theorems = theorems.as_array_mut().expect("a list");
            theorems.push(json!("Krepi.Proofs.Table.lookup_refines"));
        });
        assert_eq!(
            repeated,
            [
                "theorem Krepi.Proofs.Table.lookup_refines is registered twice: by target table, obligation lookup and by target table, obligation lookup"
            ]
        );
        let planned = broken(|registry| {
            registry["targets"][1]["obligations"] =
                json!([{"id": "o", "theorems": ["Krepi.Proofs.Table.lookup_bound"]}]);
        });
        assert_eq!(
            planned,
            [
                "theorem Krepi.Proofs.Table.lookup_bound is registered twice: by target table, obligation lookup and by target slots, obligation o"
            ]
        );
        let specified = broken(|registry| {
            table(registry)["obligations"][0]["theorems"][0] =
                json!("Krepi.Spec.Table.lookup_total");
        });
        assert_eq!(
            specified,
            [
                "theorem Krepi.Spec.Table.lookup_total is registered twice: by specification Krepi.Spec.Table and by target table, obligation lookup"
            ]
        );
    }

    #[test]
    fn a_formal_target_without_an_obligation_fails() {
        // Its mutant then names no theorem of the target.
        let problems = broken(|registry| table(registry)["obligations"] = json!([]));
        assert_eq!(
            problems,
            [
                "target table: a formal target needs an obligation",
                "target table: mutant bound names Krepi.Proofs.Table.lookup_bound, which is no theorem of the target's obligations"
            ]
        );
        // The same planned target needs none.
        let planned = broken(|registry| {
            table(registry)["obligations"] = json!([]);
            table(registry)["mutants"] = json!([]);
            table(registry)["state"] = json!("planned");
        });
        assert_eq!(planned, Vec::<String>::new());
    }

    #[test]
    fn an_obligation_without_a_theorem_fails() {
        let problems = broken(|registry| {
            let obligations = table(registry)["obligations"]
                .as_array_mut()
                .expect("a list");
            obligations.push(json!({"id": "empty", "statement": "Krepi.Statements.Table.empty"}));
        });
        assert_eq!(problems, ["target table: obligation empty has no theorem"]);
    }

    #[test]
    fn a_formal_target_without_a_mutant_fails() {
        let problems = broken(|registry| table(registry)["mutants"] = json!([]));
        assert_eq!(problems, ["target table: a formal target needs a mutant"]);
    }

    #[test]
    fn a_mutant_that_names_no_theorem_fails() {
        let problems = broken(|registry| table(registry)["mutants"][0]["fails"] = json!([]));
        assert_eq!(
            problems,
            ["target table: mutant bound names no theorem to fail"]
        );
        let problems = broken(|registry| {
            table(registry)["mutants"][0]
                .as_object_mut()
                .expect("a mutant")
                .remove("fails");
        });
        assert_eq!(
            problems,
            ["target table: mutant bound names no theorem to fail"]
        );
    }

    #[test]
    fn a_mutant_that_names_another_theorem_fails() {
        // A theorem of a specification is no theorem of the target.
        let problems = broken(|registry| {
            table(registry)["mutants"][0]["fails"] = json!([
                "Krepi.Proofs.Table.lookup_bound",
                "Krepi.Spec.Table.lookup_total"
            ]);
        });
        assert_eq!(
            problems,
            [
                "target table: mutant bound names Krepi.Spec.Table.lookup_total, which is no theorem of the target's obligations"
            ]
        );
    }

    #[test]
    fn a_key_both_proved_and_unclosed_fails() {
        let problems = broken(|registry| {
            table(registry)["unclosed"] = json!(["kernel/src/table.rs#lookup"]);
        });
        assert_eq!(
            problems,
            ["target table: kernel/src/table.rs#lookup is in proves and in unclosed"]
        );
    }

    #[test]
    fn a_key_both_proved_and_derived_fails() {
        let problems = broken(|registry| {
            table(registry)["derived"] = json!(["kernel/src/table.rs#lookup"]);
        });
        assert_eq!(
            problems,
            ["target table: kernel/src/table.rs#lookup is in proves and in derived"]
        );
    }

    #[test]
    fn a_key_both_unclosed_and_derived_fails() {
        let problems = broken(|registry| {
            table(registry)["derived"] = json!(["kernel/src/table.rs#hardware::read"]);
        });
        assert_eq!(
            problems,
            ["target table: kernel/src/table.rs#hardware::read is in unclosed and in derived"]
        );
    }

    #[test]
    fn a_library_axiom_without_its_source_or_reason_fails() {
        let axiom = |fields: Value| {
            let mut axiom = json!({"name": "Aeneas.Std.ax"});
            axiom
                .as_object_mut()
                .expect("an axiom")
                .extend(fields.as_object().expect("fields").clone());
            axiom_rules(&json!({"schema": 1, "axioms": [axiom]}).to_string())
        };
        assert_eq!(
            axiom(json!({"source": "Aeneas.Std.Core", "reason": "Used by slices."})),
            Ok(Vec::new())
        );
        assert_eq!(
            axiom(json!({"source": " \t", "reason": "Used by slices."})),
            Ok(vec!["axiom Aeneas.Std.ax has no source".to_string()])
        );
        assert_eq!(
            axiom(json!({"source": "Aeneas.Std.Core"})),
            Ok(vec!["axiom Aeneas.Std.ax has no reason".to_string()])
        );
        // A field that the gate does not know, which it refuses.
        let unknown = axiom(json!({"source": "Aeneas.Std.Core", "reason": "r", "note": "n"}));
        assert!(
            unknown
                .as_ref()
                .is_err_and(|error| error.contains("unknown field `note`")),
            "{unknown:?}"
        );
        let committed = include_str!("../../../verification/axioms.json");
        assert_eq!(axiom_rules(committed), Ok(Vec::new()));
        assert_eq!(
            axiom_rules(r#"{"schema": 2, "axioms": []}"#),
            Err("schema 2 where 1 is expected".to_string())
        );
    }

    #[test]
    fn a_cut_point_without_its_source_or_reason_fails() {
        let problems = broken(|registry| {
            let opaque = &mut table(registry)["opaque"][0];
            opaque["source"] = json!("");
            opaque
                .as_object_mut()
                .expect("a cut point")
                .remove("reason");
        });
        assert_eq!(
            problems,
            [
                "target table: opaque krepi_kernel::table::hardware::read has no source",
                "target table: opaque krepi_kernel::table::hardware::read has no reason"
            ]
        );
    }

    #[test]
    fn more_mutants_than_a_target_may_register_fail() {
        let mutants = |count: usize| {
            broken(|registry| {
                let mutant = table(registry)["mutants"][0].clone();
                table(registry)["mutants"] = Value::Array(vec![mutant; count]);
            })
        };
        assert_eq!(mutants(MUTANTS), Vec::<String>::new());
        assert_eq!(
            mutants(MUTANTS + 1),
            ["target table: 31 mutants, more than the 30 that a target may register"]
        );
    }

    /// An empty model registry.
    const NO_MODELS: &str = r#"{"schema": 1, "models": []}"#;

    /// The problems of the gate's check for the planned target `target`.
    fn unsupported(target: &str) -> Vec<String> {
        let targets = format!(r#"{{"schema": 2, "targets": [{target}]}}"#);
        check(&targets, NO_MODELS).expect("valid registries").1
    }

    #[test]
    fn the_rules_and_the_refusals_are_checked_together() {
        let (registry, problems) = check(&valid().to_string(), NO_MODELS).expect("valid");
        assert_eq!((registry.targets.len(), problems), (2, Vec::new()));
        for models in [r#"{"schema": 2, "models": []}"#, r#"{"schema": 1}"#, "[]"] {
            let error = check(&valid().to_string(), models).expect_err("not a model registry");
            assert_eq!(error, "not a model registry of schema 1", "{models}");
        }
        assert_eq!(
            unsupported(r#"{"name": "a", "mutants": []}"#),
            [
                "target a: a formal target needs an obligation",
                "target a: a formal target needs a mutant"
            ]
        );
    }

    #[test]
    fn non_empty_premises_are_refused() {
        assert_eq!(
            unsupported(r#"{"name": "a", "state": "planned", "premises": [{}]}"#),
            ["target a: premises are not supported yet"]
        );
    }

    #[test]
    fn a_non_empty_model_registry_is_refused() {
        let models = r#"{"schema": 1, "models": [{"name": "m"}]}"#;
        let (_, unsupported) = check(r#"{"schema": 2, "targets": []}"#, models).expect("valid");
        assert_eq!(
            unsupported,
            ["models are not compared with their implementations yet"]
        );
    }

    #[test]
    fn exclude_cut_points_are_refused() {
        assert_eq!(
            unsupported(r#"{"name": "a", "state": "planned", "exclude": ["k::f"]}"#),
            ["target a: exclude is not supported yet"]
        );
        // The committed registries register nothing that the gate refuses.
        let (registry, problems) = check(
            include_str!("../../../verification/targets.json"),
            include_str!("../../../verification/models.json"),
        )
        .expect("the committed registries");
        assert_eq!((registry.targets.len(), problems), (0, Vec::new()));
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
