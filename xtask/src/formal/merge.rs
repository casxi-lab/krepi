//! The shards of the proof gate, as "Shard plan and disk guard" in
//! `docs/formal-verification.md` describes: every formal target is a shard
//! of its own, named by its unit, and the registered budget of a shard, over
//! its workers, is at most the shard limit, the wall-clock limit of the gate
//! less the time of the merge. `cargo xtask formal check` applies the limit;
//! `cargo xtask formal merge` (planned) is to combine the receipts of the
//! shards.

use std::collections::BTreeMap;
use std::time::Duration;

use super::registry::{State, Target};
use super::run;

/// The wall-clock limit of the gate, from the start of its first job to the
/// end of its merge.
pub const WALL_CLOCK: Duration = Duration::from_secs(3_600);

/// The time of the merge, from the start of its job to the end of
/// `cargo xtask formal merge`.
pub const MERGE: Duration = Duration::from_secs(300);

/// The longest that a shard may take: the wall-clock limit less the merge.
pub const SHARD_LIMIT: Duration = Duration::from_secs(WALL_CLOCK.as_secs() - MERGE.as_secs());

/// The workers of a shard, among which its registered budget is divided.
pub const WORKERS: u64 = 1;

/// The shards of the formal targets of `targets`, by name, each with the sum
/// of the registered budgets of its targets: every formal target is a shard
/// of its own, named by its unit.
pub fn shards(targets: &[Target]) -> BTreeMap<String, u64> {
    let mut shards = BTreeMap::new();
    for target in targets.iter().filter(|t| t.state == State::Formal) {
        let budget: &mut u64 = shards.entry(run::target_unit(&target.name)).or_default();
        *budget = budget.saturating_add(target.budget);
    }
    shards
}

/// The problems of the shards of `targets`: a shard whose registered
/// budget per worker, rounded up, is more than the shard limit.
pub fn budget_problems(targets: &[Target]) -> Vec<String> {
    let limit = SHARD_LIMIT.as_secs();
    let over = shards(targets).into_iter().filter_map(|(shard, budget)| {
        let seconds = budget.div_ceil(WORKERS);
        (seconds > limit).then(|| {
            format!(
                "shard {shard}: its registered budget of {budget} s is {seconds} s per worker, more than the shard limit of {limit} s"
            )
        })
    });
    over.collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formal::registry;

    /// The targets of the registry `text`.
    fn targets(text: &str) -> Vec<Target> {
        registry::parse(text).expect("a registry").targets
    }

    #[test]
    fn the_shard_limit_is_the_wall_clock_limit_of_the_gate_less_the_merge() {
        assert_eq!(SHARD_LIMIT, Duration::from_secs(3_300));
        assert_eq!(MERGE + SHARD_LIMIT, WALL_CLOCK);
        assert_eq!(WORKERS, 1);
    }

    #[test]
    fn the_committed_registries_keep_the_shard_limit() {
        let production = targets(include_str!("../../../verification/targets.json"));
        assert_eq!(budget_problems(&production), Vec::<String>::new());
        assert!(shards(&production).is_empty());
        let calibration = targets(include_str!(
            "../../../verification/qualification/calibration/targets.json"
        ));
        assert_eq!(budget_problems(&calibration), Vec::<String>::new());
        // The planned target of the calibration is no shard.
        assert_eq!(
            shards(&calibration),
            BTreeMap::from([("target/calibration".to_string(), 3_000)])
        );
    }

    #[test]
    fn each_formal_target_is_a_shard_of_its_own_with_its_registered_budget() {
        let registry = |budget: u64| {
            targets(&format!(
                r#"{{"schema": 2, "targets": [
                    {{"name": "a", "budget": {budget}}}, {{"name": "b"}},
                    {{"name": "p", "state": "planned", "budget": 9999}}]}}"#
            ))
        };
        assert_eq!(
            shards(&registry(3_300)),
            BTreeMap::from([
                ("target/a".to_string(), 3_300),
                ("target/b".to_string(), registry::BUDGET)
            ])
        );
        assert_eq!(budget_problems(&registry(3_300)), Vec::<String>::new());
        assert_eq!(
            budget_problems(&registry(3_301)),
            [
                "shard target/a: its registered budget of 3301 s is 3301 s per worker, more than the shard limit of 3300 s"
            ]
        );
    }
}
