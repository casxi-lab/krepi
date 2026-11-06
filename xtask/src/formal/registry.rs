//! The proof target registry, `verification/targets.json`, as far as the
//! gate reads it: the names of the registered targets.

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
}
