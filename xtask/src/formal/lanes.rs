//! The lanes of the base round, `verification/lanes.json`, as "Lanes" in
//! `docs/formal-verification.md` describes: the components and the shared
//! hand-written modules of each lane, with its registered budget, and the
//! rules that `cargo xtask formal check` applies to them.

use std::collections::{BTreeMap, BTreeSet};

use serde::Deserialize;
use serde_json::Value;

use super::merge::{EXTRACTION_MARGIN, SHARD_LIMIT};
use super::registry::{State, Target};

/// The schema of the lanes.
pub const SCHEMA: u32 = 1;

/// The budget of a lane that registers none, in seconds.
pub const BUDGET: u64 = 2_400;

/// The layers of the Lake project, directories below its namespace, in each
/// of which a component has a directory of its own.
pub const LAYERS: &str = "Spec SpecProperties SpecTests Statements Proofs";

/// The lanes, `verification/lanes.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
#[expect(dead_code, reason = "the schema is read before the lanes")]
pub struct Lanes {
    pub schema: u32,
    pub lanes: Vec<Lane>,
}

/// A lane: its name, its components, the shared hand-written modules that it
/// holds and its registered budget.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Lane {
    pub name: String,
    pub components: Vec<String>,
    #[serde(default)]
    pub modules: Vec<String>,
    #[serde(default = "budget")]
    pub budget: u64,
}

fn budget() -> u64 {
    BUDGET
}

/// Where a hand-written module belongs, by its file: to the qualification
/// job, to the lane of its component, or, as a shared module outside both,
/// to the lane that lists it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Home {
    Qualification,
    Component(String),
    Shared,
}

/// The hand-written modules of a Lake project, by name, with their homes.
pub type Homes = BTreeMap<String, Home>;

/// The lanes `text` of schema [`SCHEMA`].
pub fn parse(text: &str) -> Result<Lanes, String> {
    let not = |error: serde_json::Error| format!("not a record of lanes: {error}");
    let value: Value = serde_json::from_str(text).map_err(not)?;
    let schema = &value["schema"];
    if schema != SCHEMA {
        return Err(format!("schema {schema} where {SCHEMA} is expected"));
    }
    serde_json::from_value(value).map_err(not)
}

/// The problems of the lanes `text` at `path` with the hand-written modules
/// `homes` and the registry's `targets`: lanes that cannot be read; a lane
/// name not of lowercase letters, digits and hyphens that starts with a
/// letter or a digit, or that of another lane; a component or a listed module
/// in two lanes, or twice in one; a listed module that is no shared module; a
/// budget that with the extraction margin is more than the shard limit; a
/// component of a hand-written module in no lane; a shared module in no lane,
/// or shared modules, which are one component, in two lanes; and a formal
/// target whose module is in no lane.
pub fn check(path: &str, text: &str, homes: &Homes, targets: &[Target]) -> Vec<String> {
    let lanes = match parse(text) {
        Ok(lanes) => lanes.lanes,
        Err(error) => return vec![format!("{path}: {error}")],
    };
    let (limit, margin) = (SHARD_LIMIT.as_secs(), EXTRACTION_MARGIN.as_secs());
    let (mut problems, mut names) = (Vec::new(), BTreeSet::new());
    let (mut components, mut listed) = (BTreeMap::new(), BTreeMap::new());
    for lane in &lanes {
        let (name, budget) = (&lane.name, lane.budget);
        let mut problem = |what: String| problems.push(format!("{path}: lane {name}: {what}"));
        let first = |c: char| c.is_ascii_lowercase() || c.is_ascii_digit();
        if !name.starts_with(first) || !name.chars().all(|c| first(c) || c == '-') {
            problem("its name does not match [a-z0-9][a-z0-9-]*".into());
        }
        if !names.insert(name) {
            problem("another lane has its name".into());
        }
        for component in &lane.components {
            if let Some(other) = components.insert(component, name) {
                problem(format!("component {component} is in lane {other} already"));
            }
        }
        for module in &lane.modules {
            if let Some(other) = listed.insert(module, name) {
                problem(format!("module {module} is in lane {other} already"));
            }
            if homes.get(module) != Some(&Home::Shared) {
                problem(format!("module {module} is no shared hand-written module"));
            }
        }
        if budget.saturating_add(margin) > limit {
            problem(format!(
                "its registered budget of {budget} s and the extraction margin of {margin} s are more than the shard limit of {limit} s"
            ));
        }
    }
    let unheld = homes.values().filter_map(|home| match home {
        Home::Component(component) => (!components.contains_key(component)).then_some(component),
        _ => None,
    });
    let unheld = BTreeSet::from_iter(unheld).into_iter();
    problems.extend(unheld.map(|c| format!("{path}: component {c} is in no lane")));
    let shared = homes.iter().filter(|(_, home)| **home == Home::Shared);
    let unlisted = shared.clone().filter(|(m, _)| !listed.contains_key(*m));
    problems.extend(unlisted.map(|(m, _)| format!("{path}: shared module {m} is in no lane")));
    let holding = shared.filter_map(|(module, _)| listed.get(module).map(|lane| lane.as_str()));
    let holding = Vec::from_iter(BTreeSet::from_iter(holding));
    if holding.len() > 1 {
        let holding = holding.join(", ");
        problems.push(format!(
            "{path}: the shared modules are in more than one lane: {holding}"
        ));
    }
    let held = |m: &Option<String>| m.as_ref().is_some_and(|m| components.contains_key(m));
    let lost = |t: &&Target| t.state == State::Formal && !held(&t.module);
    let lost = targets.iter().filter(lost).map(|t| &t.name);
    problems.extend(lost.map(|name| format!("{path}: target {name}: its module is in no lane")));
    problems
}

#[cfg(test)]
mod tests {
    use serde_json::{Value, json};

    use super::*;
    use crate::formal::{Layout, guard, inventory, registry};
    use crate::repo::{self, Tree};

    /// The path of the lanes of the tests.
    const PATH: &str = "L";

    /// The hand-written modules of the tests: two of `Fdt`, one of
    /// `PageTables`, the shared `Krepi.Statements.Basic` and one of the
    /// qualification.
    fn homes() -> Homes {
        let component = |name: &str| Home::Component(name.to_string());
        BTreeMap::from_iter(
            [
                ("Krepi.Proofs.Fdt.A", component("Fdt")),
                ("Krepi.Spec.Fdt.B", component("Fdt")),
                ("Krepi.Spec.PageTables.C", component("PageTables")),
                ("Krepi.Statements.Basic", Home::Shared),
                ("Krepi.Qualification.Arithmetic", Home::Qualification),
            ]
            .map(|(module, home)| (module.to_string(), home)),
        )
    }

    /// The lane `fdt`, with the shared module, and the lane `page-tables`.
    fn two_lanes() -> Value {
        json!([
            {"name": "fdt", "components": ["Fdt"], "modules": ["Krepi.Statements.Basic"], "budget": 1000},
            {"name": "page-tables", "components": ["PageTables"]},
        ])
    }

    /// A target of `state` with `module`.
    fn target(name: &str, state: &str, module: Option<&str>) -> Target {
        let target = json!({"name": name, "state": state, "module": module});
        serde_json::from_value(target).expect("a target")
    }

    /// The problems of `lanes` with [`homes`] and `targets`.
    fn problems(lanes: &Value, targets: &[Target]) -> Vec<String> {
        let text = json!({"schema": 1, "lanes": lanes}).to_string();
        check(PATH, &text, &homes(), targets)
    }

    #[test]
    fn lanes_that_hold_each_module_once_have_no_problem() {
        // The qualification module needs no lane, and a planned target no
        // lane of its module.
        let targets = [
            target("fdt", "formal", Some("Fdt")),
            target("other", "planned", Some("Other")),
        ];
        assert_eq!(problems(&two_lanes(), &targets), Vec::<String>::new());
        // A lane without a budget has the default.
        let text = json!({"schema": 1, "lanes": two_lanes()}).to_string();
        let lanes = parse(&text).expect("lanes");
        let budgets = Vec::from_iter(lanes.lanes.iter().map(|lane| lane.budget));
        assert_eq!((budgets, BUDGET), (vec![1_000, BUDGET], 2_400));
    }

    #[test]
    fn lanes_that_cannot_be_read_are_one_problem() {
        let read = |text: &str| check(PATH, text, &homes(), &[]);
        let unknown = json!({"schema": 1, "lanes": [{"name": "a", "components": [], "extra": 1}]});
        for (text, start) in [
            ("{", "L: not a record of lanes: "),
            (
                r#"{"schema": 2, "lanes": []}"#,
                "L: schema 2 where 1 is expected",
            ),
            (
                &unknown.to_string(),
                "L: not a record of lanes: unknown field `extra`",
            ),
        ] {
            let problems = read(text);
            assert!(
                problems.len() == 1 && problems[0].starts_with(start),
                "{problems:?}"
            );
        }
    }

    #[test]
    fn a_lane_name_is_of_lowercase_letters_digits_and_hyphens_and_unique() {
        let mut lanes = two_lanes();
        for (name, problem) in [
            (
                "Fdt",
                "L: lane Fdt: its name does not match [a-z0-9][a-z0-9-]*",
            ),
            (
                "-fdt",
                "L: lane -fdt: its name does not match [a-z0-9][a-z0-9-]*",
            ),
            (
                "page-tables",
                "L: lane page-tables: another lane has its name",
            ),
        ] {
            lanes[0]["name"] = json!(name);
            assert_eq!(problems(&lanes, &[]), [problem]);
        }
        lanes[0]["name"] = json!("0-fdt");
        assert_eq!(problems(&lanes, &[]), Vec::<String>::new());
    }

    #[test]
    fn a_component_or_a_listed_module_is_in_one_lane() {
        let mut lanes = two_lanes();
        lanes[1]["components"] = json!(["PageTables", "Fdt"]);
        assert_eq!(
            problems(&lanes, &[]),
            ["L: lane page-tables: component Fdt is in lane fdt already"]
        );
        let mut lanes = two_lanes();
        lanes[0]["components"] = json!(["Fdt", "Fdt"]);
        lanes[0]["modules"] = json!(["Krepi.Statements.Basic", "Krepi.Statements.Basic"]);
        assert_eq!(
            problems(&lanes, &[]),
            [
                "L: lane fdt: component Fdt is in lane fdt already",
                "L: lane fdt: module Krepi.Statements.Basic is in lane fdt already",
            ]
        );
    }

    #[test]
    fn a_lane_lists_shared_hand_written_modules_alone() {
        let mut lanes = two_lanes();
        let modules = [
            "Krepi.Proofs.Fdt.A",
            "Krepi.Qualification.Arithmetic",
            "Krepi.Gone",
        ];
        lanes[1]["modules"] = json!(modules);
        let not = "is no shared hand-written module";
        let expected = modules.map(|module| format!("L: lane page-tables: module {module} {not}"));
        assert_eq!(problems(&lanes, &[]), expected);
    }

    #[test]
    fn a_component_of_a_hand_written_module_is_in_a_lane() {
        let lanes = json!([
            {"name": "page-tables", "components": ["PageTables"], "modules": ["Krepi.Statements.Basic"]},
        ]);
        // One problem for the component, whatever its modules.
        assert_eq!(problems(&lanes, &[]), ["L: component Fdt is in no lane"]);
        // A component without a hand-written module may be in a lane.
        let mut lanes = two_lanes();
        lanes[1]["components"] = json!(["PageTables", "Objects"]);
        assert_eq!(problems(&lanes, &[]), Vec::<String>::new());
    }

    #[test]
    fn the_module_of_each_formal_target_is_a_component_of_a_lane() {
        let targets = [
            target("fdt", "formal", Some("Fdt")),
            target("objects", "formal", Some("Objects")),
            target("bare", "formal", None),
            target("planned", "planned", None),
        ];
        assert_eq!(
            problems(&two_lanes(), &targets),
            [
                "L: target objects: its module is in no lane",
                "L: target bare: its module is in no lane",
            ]
        );
    }

    #[test]
    fn the_job_formal_limits_refuses_the_lanes_that_formal_check_refuses() {
        // `formal.yml` checks the lanes with these numbers and lines, which
        // are those of xtask: the default budget, the extraction margin and
        // the shard limit, compared as `check` compares them.
        let formal = include_str!("../../../.github/workflows/formal.yml");
        let lines = [
            format!("shard_limit={}", SHARD_LIMIT.as_secs()),
            format!("extraction_margin={}", EXTRACTION_MARGIN.as_secs()),
            format!("lanes={}", Layout::PRODUCTION.lanes),
            r#"jq -e 'all(.lanes[]; .name | test("^[a-z0-9][a-z0-9-]*$"))' "$lanes" > /dev/null"#
                .to_string(),
            r#"heavy=$(jq -r --argjson margin "$extraction_margin" --argjson limit "$shard_limit" \"#
                .to_string(),
            format!(
                r#"'[.lanes[] | select((.budget // {BUDGET}) + $margin > $limit) | .name] | join(" ")' "$lanes")"#
            ),
            r#"if [ -n "$heavy" ]; then"#.to_string(),
            r#"echo "the registered budget of the lane $heavy and the extraction margin of $extraction_margin s are more than $shard_limit s" >&2"#
                .to_string(),
        ];
        for line in &lines {
            assert!(formal.lines().any(|l| l.trim_start() == line), "{line}");
        }
        // The job refuses a lane of a budget above 2,700 s, and so does the
        // check, which takes the name rule of the job too.
        let budget = SHARD_LIMIT.as_secs() - EXTRACTION_MARGIN.as_secs();
        assert_eq!(budget, 2_700);
        let mut lanes = two_lanes();
        lanes[0]["budget"] = json!(budget);
        assert_eq!(problems(&lanes, &[]), Vec::<String>::new());
        lanes[0]["budget"] = json!(budget + 1);
        assert_eq!(
            problems(&lanes, &[]),
            [
                "L: lane fdt: its registered budget of 2701 s and the extraction margin of 600 s are more than the shard limit of 3300 s"
            ]
        );
    }

    #[test]
    fn the_committed_lanes_hold_the_hand_written_modules_of_both_layouts() {
        let tree = Tree::load(&repo::root()).expect("the repository is readable");
        for layout in [Layout::PRODUCTION, Layout::CALIBRATION] {
            let homes = inventory::homes(&tree, &layout);
            let text = tree.text(layout.lanes).expect("the lanes are tracked");
            let registry = tree.text(layout.registry).expect("the registry is tracked");
            let targets = registry::parse(registry).expect("a registry").targets;
            assert_eq!(
                check(layout.lanes, text, &homes, &targets),
                Vec::<String>::new()
            );
            // The lanes are not on the statement side, so that a change of
            // them needs no label of a specification.
            assert!(
                !guard::statement_side(layout.lanes, &layout),
                "{}",
                layout.lanes
            );
        }
    }
}
