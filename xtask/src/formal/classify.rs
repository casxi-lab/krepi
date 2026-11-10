//! The registration check of a proof target: what an extraction reaches
//! against what the target registers, as "Proof targets" in
//! `docs/formal-verification.md` describes it. Every reached local
//! function, translated or cut, maps from its Rust name to the key of the
//! function in the inventory of `cargo xtask formal check`; a generated
//! function that maps to no key, such as the body of a closure or a loop
//! that the tools place in the file of a macro, is not registered, and
//! neither is one whose key cannot tell it from another function or a
//! derived method of its file. The checks and the mapping are those of the
//! CAS project.
#![cfg_attr(
    not(test),
    expect(dead_code, reason = "the target phase of the gate is the first caller")
)]

use std::collections::{BTreeMap, BTreeSet};

use super::extract::Extraction;
use super::inventory::{self, Inventory};
use super::registry::Target;
use crate::repo;

/// A reached local function: its inventory key and its Rust name.
type Local = (String, String);

/// The keys of the local functions that an extraction translates and cuts,
/// and the Rust names of the external items that it reaches.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Classification {
    pub transparent: Vec<String>,
    pub opaque: Vec<String>,
    pub external: Vec<String>,
}

/// Checks the extraction of `target` from the package in the directory
/// `package`, relative to the repository root, against the registry and
/// the inventory: reached local functions, cut points and external items
/// must all be accounted for. Local functions are identified by their
/// inventory key (`file#Owner::name`). Returns the problems and what was
/// found.
pub fn classify(
    target: &Target,
    extraction: &Extraction,
    package: &str,
    inventory: &Inventory,
) -> (Vec<String>, Classification) {
    let mut problems = Vec::new();
    let mut keyed = |opaque: bool| -> Vec<Local> {
        let mut locals = Vec::new();
        for (rust_name, file, lean_name) in extraction.local_functions(opaque) {
            match key_of(package, &file, &rust_name, &lean_name, inventory) {
                Ok(key) => locals.push((key, rust_name)),
                Err(problem) => problems.push(format!(
                    "{}: reached local function {rust_name} ({lean_name}) is not registered: {problem}",
                    target.name
                )),
            }
        }
        locals
    };
    let (translated, cut) = (keyed(false), keyed(true));
    let cut_names: BTreeSet<String> = (extraction.local_functions(true).into_iter())
        .map(|(rust_name, _, _)| rust_name)
        .collect();
    let external: BTreeSet<String> = (extraction.external_functions().into_iter())
        .chain(extraction.external_types())
        .filter(|name| !cut_names.contains(name))
        .collect();
    let (found, classification) = classify_items(target, &translated, &cut, &external);
    problems.extend(found);
    (problems, classification)
}

/// The inventory key of the local function `rust_name`, `lean_name` in
/// Lean, that the tools report in `file`, relative to the package in
/// `package`, or why it has none. A key that the inventory holds both as a
/// function and as a derived method is the key of neither: under `proves`,
/// the hand-written function would stand for the derived method too.
fn key_of(
    package: &str,
    file: &str,
    rust_name: &str,
    lean_name: &str,
    inventory: &Inventory,
) -> Result<String, String> {
    if rust_name.contains("{closure") {
        return Err("the body of a closure has no inventory key, so a target can neither prove nor register it; write the code without the closure, as the rule on closures as callbacks (R4) of the provable subset says".to_string());
    }
    let path = repo::join(package, file).filter(|path| repo::is_within(path, package));
    let modules = path.as_ref().and_then(|path| inventory.modules.get(path));
    let (Some(path), Some(modules)) = (path, modules) else {
        return Err(format!(
            "the tools place it in {file}, which is no production file of the package, so it has no inventory key; a loop condition calls a function rather than a macro, as the loop shapes of the provable subset say"
        ));
    };
    let krate = rust_name.split("::").next().unwrap_or_default();
    let key = |module| key_for_translated(&path, rust_name, lean_name, krate, module);
    let keys: BTreeSet<String> = modules.iter().filter_map(|module| key(module)).collect();
    let known =
        |key: &&String| inventory.functions.contains(*key) || inventory.derived.contains(*key);
    match keys.iter().filter(known).collect::<Vec<_>>()[..] {
        [key] if inventory.functions.contains(&format!("{key}#2")) => Err(format!(
            "it maps to {key}, the key of more than one method of trait implementations in {path}, which its name does not tell apart"
        )),
        [key] if inventory.functions.contains(key) && inventory.derived.contains(key) => {
            Err(format!(
                "it maps to {key}, the key of both a function and a derived method in {path}, which the key does not tell apart"
            ))
        }
        [key] => Ok(key.clone()),
        _ if keys.is_empty() => Err(format!("its name is not below the module of {path}")),
        _ => Err(format!(
            "it maps to {}, not to exactly one function of the inventory",
            Vec::from_iter(keys).join(" or ")
        )),
    }
}

/// [`classify`] on the local functions of an extraction, translated and cut,
/// as `(key, rust name)`, and the Rust names of its external functions and
/// types that are not local. Returns the problems and the classification.
fn classify_items(
    target: &Target,
    translated: &[Local],
    cut: &[Local],
    outside: &BTreeSet<String>,
) -> (Vec<String>, Classification) {
    // Each key with the Rust names that map to it.
    let keys = |items: &[Local]| -> BTreeMap<String, BTreeSet<String>> {
        let mut keys: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (key, name) in items {
            keys.entry(key.clone()).or_default().insert(name.clone());
        }
        keys
    };
    let transparent = keys(translated);
    let local_cuts = keys(cut);
    let mut problems = Vec::new();
    let name = &target.name;
    // A derived entry stands for one derived method: a key that several Rust
    // names reach is not accepted. `key_of` already refuses the key of the
    // derived `eq` of a type that also implements `PartialEq<u32>` by hand,
    // which is the key of a function of the inventory too; this refuses any
    // other key that several names reach.
    for key in &target.derived {
        let reached: BTreeSet<&String> = transparent
            .get(key)
            .into_iter()
            .chain(local_cuts.get(key))
            .flatten()
            .collect();
        if reached.len() > 1 {
            let names: Vec<&str> = reached.iter().map(|name| name.as_str()).collect();
            problems.push(format!(
                "{name}: derived entry {key} is reached under several Rust names: {}",
                names.join(", ")
            ));
        } else if let Some(rust_name) = reached.first()
            && !is_derived_name(rust_name)
        {
            problems.push(format!(
                "{name}: derived entry {key} is reached as {rust_name}, which is not a derived method"
            ));
        }
    }
    for key in transparent.keys() {
        if !target.proves.contains(key)
            && !target.unclosed.contains(key)
            && !target.derived.contains(key)
        {
            problems.push(format!(
                "{name}: reached local function {key} is neither proved nor registered as unclosed"
            ));
        }
    }
    for key in local_cuts.keys() {
        if !target.unclosed.contains(key) && !target.derived.contains(key) {
            problems.push(format!(
                "{name}: opaque local item {key} must be registered as unclosed"
            ));
        }
    }
    for key in &target.proves {
        if !transparent.contains_key(key) {
            problems.push(format!(
                "{name}: proved function {key} is not translated by this extraction"
            ));
        }
    }
    for key in &target.unclosed {
        if !transparent.contains_key(key) && !local_cuts.contains_key(key) {
            problems.push(format!(
                "{name}: unclosed entry {key} is not reached by this extraction"
            ));
        }
    }
    for key in &target.derived {
        if !transparent.contains_key(key) && !local_cuts.contains_key(key) {
            problems.push(format!(
                "{name}: derived entry {key} is not reached by this extraction"
            ));
        }
    }
    let registered: BTreeSet<String> = target.unconstrained.iter().cloned().collect();
    for item in outside.difference(&registered) {
        problems.push(format!("{name}: external item {item} is not registered"));
    }
    for item in registered.difference(outside) {
        problems.push(format!(
            "{name}: registered external item {item} is not reached"
        ));
    }
    let classification = Classification {
        transparent: transparent.into_keys().collect(),
        opaque: local_cuts.into_keys().collect(),
        external: outside.iter().cloned().collect(),
    };
    (problems, classification)
}

/// The inventory key of an Aeneas Rust name such as
/// `krepi_kernel::m::{krepi_kernel::m::Type}::f` or
/// `krepi_kernel::m::{impl Trait for krepi_kernel::m::Type}::f`, given the
/// source file reported for it and the crate `krate` and module `module` of
/// that file, such as `m`, or empty for the root of the crate. The segments
/// between the module and the item are the inline modules of the key, as
/// in `file#inner::Type::f`. `None` when the name is not below the module.
pub fn key_for_rust_name(file: &str, rust_name: &str, krate: &str, module: &str) -> Option<String> {
    let below = rust_name.strip_prefix(&below(krate, module))?;
    let mut name = below.to_string();
    let mut owner = None;
    let mut inline = "";
    if let (Some(open), Some(close)) = (below.find('{'), closing(below)) {
        let inner = &below[open + 1..close];
        let inner = inner.rsplit(" for ").next().unwrap_or(inner);
        let inner = inner.split('<').next().unwrap_or(inner);
        owner = inner.rsplit("::").next().map(str::to_string);
        name = below[close + 1..].trim_start_matches("::").to_string();
        inline = &below[..open];
    }
    let simple = name.rsplit("::").next().unwrap_or(&name).to_string();
    match owner {
        Some(owner) => Some(format!("{file}#{inline}{owner}::{simple}")),
        None => Some(format!("{file}#{name}")),
    }
}

/// The prefix of the Rust names of the items in the module `module` of the
/// crate `krate`.
fn below(krate: &str, module: &str) -> String {
    match module {
        "" => format!("{krate}::"),
        module => format!("{krate}::{module}::"),
    }
}

/// The index of the brace that closes the first `{` of `name`.
fn closing(name: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (index, c) in name.char_indices() {
        match c {
            '{' => depth += 1,
            '}' if depth == 1 => return Some(index),
            '}' => depth = depth.checked_sub(1)?,
            _ => {}
        }
    }
    None
}

/// The inventory key of a function in Aeneas's `translation.json`, given its
/// Rust name, source file and Lean name, and the crate and module of the
/// file. A default method of a trait has a Rust name without an
/// implementation, `krepi_kernel::m::Trait::method`, and the Lean name
/// `….Trait.method.default`; Aeneas names its loops `….method.default_loop`,
/// or `default_loop0`, `default_loop1` and so on when it has several, and
/// their bodies with a further `.body`. Its key is `file#Trait::method`, the
/// name that the inventory gives the method inside the trait, after the
/// inline modules between the module and the trait. Every other name maps
/// as in [`key_for_rust_name`].
pub fn key_for_translated(
    file: &str,
    rust_name: &str,
    lean_name: &str,
    krate: &str,
    module: &str,
) -> Option<String> {
    if !rust_name.contains('{') {
        let below = rust_name.strip_prefix(&below(krate, module))?;
        let mut segments = below.rsplitn(3, "::");
        if let (Some(method), Some(owner)) = (segments.next(), segments.next())
            && is_default_method(method, lean_name)
        {
            let inline = segments
                .next()
                .map_or(String::new(), |inline| inline.to_string() + "::");
            return Some(format!("{file}#{inline}{owner}::{method}"));
        }
    }
    key_for_rust_name(file, rust_name, krate, module)
}

/// Whether `lean_name` is the definition of the default method `method` of a
/// trait or one of its loops (see [`key_for_translated`]).
fn is_default_method(method: &str, lean_name: &str) -> bool {
    let lean_name = lean_name.strip_suffix(".body").unwrap_or(lean_name);
    let mut segments = lean_name.rsplit('.');
    let (Some(last), Some(named)) = (segments.next(), segments.next()) else {
        return false;
    };
    let default = last == "default"
        || last
            .strip_prefix("default_loop")
            .is_some_and(|index| index.bytes().all(|byte| byte.is_ascii_digit()));
    default && named == method
}

/// Whether an Aeneas Rust name is the method that a derive defines in an
/// implementation of a standard trait, such as
/// `krepi_kernel::m::{impl core::clone::Clone for krepi_kernel::m::Type}::clone`.
/// A hand-written implementation has the same form; only the source tells
/// them apart (see [`derived_problems`]).
pub fn is_derived_name(rust_name: &str) -> bool {
    let (Some(open), Some(close)) = (rust_name.rfind('{'), rust_name.rfind('}')) else {
        return false;
    };
    if open > close {
        return false;
    }
    let Some(implemented) = rust_name[open + 1..close].strip_prefix("impl core::") else {
        return false;
    };
    let Some((path, _)) = implemented.split_once(" for ") else {
        return false;
    };
    let path = path.split('<').next().unwrap_or(path);
    let trait_name = path.rsplit("::").next().unwrap_or(path);
    let method = rust_name[close + 1..].trim_start_matches("::");
    let mut pairs = inventory::DERIVED.split(' ');
    pairs.any(|pair| pair.split_once(':') == Some((trait_name, method)))
}

/// Problems with the `derived` entries of `target`: each must name a method
/// that a `#[derive(..)]` attribute of a production type in its file
/// defines, as the inventory records it, and none may be a production
/// function, which would be hand-written and belongs under `proves` or
/// `unclosed`.
pub fn derived_problems(target: &Target, inventory: &Inventory) -> Vec<String> {
    let mut problems = Vec::new();
    for key in &target.derived {
        if inventory.functions.contains(key) {
            problems.push(format!(
                "target {}: derived entry {key} is a production function",
                target.name
            ));
            continue;
        }
        let Some((file, _)) = key.split_once('#') else {
            problems.push(format!(
                "target {}: derived entry {key} is not a key `file#Type::method`",
                target.name
            ));
            continue;
        };
        if !inventory.derived.contains(key) {
            problems.push(format!(
                "target {}: derived entry {key} matches no #[derive] attribute in {file}",
                target.name
            ));
        }
    }
    problems
}

#[cfg(test)]
mod tests {
    //! The translations of `fixtures/classify/` are what the pinned Charon
    //! and Aeneas wrote, with the arguments of the extraction of a
    //! qualification case, on `darwin-arm64` for four modules of the crate
    //! whose sources are in `fixtures/classify/src/`: `registration`,
    //! extracted with `--opaque crate::registration::hardware::read`,
    //! `names`, `closure` and `scan`. The tests place the crate at
    //! `kernel/`, as the root package of the kernel workspace.

    use std::path::PathBuf;

    use serde_json::{Value, json};

    use super::*;
    use crate::formal::extract::Translation;
    use crate::formal::registry;
    use crate::repo::Tree;

    /// The directory of the crate.
    const PACKAGE: &str = "kernel";

    /// The sources of the crate, below [`PACKAGE`].
    const SOURCES: [(&str, &str); 5] = [
        (
            "kernel/src/lib.rs",
            include_str!("fixtures/classify/src/lib.rs"),
        ),
        (
            "kernel/src/registration.rs",
            include_str!("fixtures/classify/src/registration.rs"),
        ),
        (
            "kernel/src/names.rs",
            include_str!("fixtures/classify/src/names.rs"),
        ),
        (
            "kernel/src/closure.rs",
            include_str!("fixtures/classify/src/closure.rs"),
        ),
        (
            "kernel/src/scan.rs",
            include_str!("fixtures/classify/src/scan.rs"),
        ),
    ];

    const REGISTRATION: &str = include_str!("fixtures/classify/registration/translation.json");
    const NAMES: &str = include_str!("fixtures/classify/names/translation.json");
    const CLOSURE: &str = include_str!("fixtures/classify/closure/translation.json");
    const SCAN: &str = include_str!("fixtures/classify/scan/translation.json");

    /// The file of the registration module.
    const FILE: &str = "kernel/src/registration.rs";

    /// The file of the names module.
    const NAMES_FILE: &str = "kernel/src/names.rs";

    /// The inventory of the crate.
    fn crate_inventory() -> Inventory {
        let roots = [("kernel/src/lib.rs".to_string(), true)];
        let (inventory, problems) =
            inventory::inventory(&Tree::from_files(&SOURCES), &roots, PACKAGE);
        assert_eq!(problems, BTreeSet::new());
        inventory
    }

    /// The extraction of `module` whose translation is `text`.
    fn extraction(module: &str, text: &str) -> Extraction {
        let translation: Translation = serde_json::from_str(text).expect("a captured translation");
        Extraction {
            complete: true,
            diagnostics: Vec::new(),
            namespace: format!("KrepiGen.Reg.{module}"),
            generated: PathBuf::from("aeneas"),
            files: BTreeMap::new(),
            translation,
        }
    }

    /// The planned target `fields` registers.
    fn target(fields: Value) -> Target {
        let mut target = json!({"name": "reg", "state": "planned"});
        let object = target.as_object_mut().expect("a target");
        object.extend(fields.as_object().expect("the fields").clone());
        let registry = json!({"schema": 2, "targets": [target]});
        let registry = registry::parse(&registry.to_string()).expect("a registry");
        registry.targets.into_iter().next().expect("the target")
    }

    /// The keys of `names` in the file of the registration module.
    fn keys(names: &[&str]) -> Vec<String> {
        names.iter().map(|name| format!("{FILE}#{name}")).collect()
    }

    /// The functions of the names module that its extraction translates,
    /// but for `eq`, whose key is also that of a derived method.
    fn names_proved() -> Vec<String> {
        let names = [
            "Count::default",
            "Count::twice",
            "Wrapper::count",
            "Wrapper::get",
            "default",
            "equal",
        ];
        (names.iter())
            .map(|name| format!("{NAMES_FILE}#{name}"))
            .collect()
    }

    /// What the registration target registers, as its extraction requires.
    fn registration() -> Value {
        json!({
            "proves": keys(&[
                "Slots::bump", "Slots::value", "Table::total", "same", "copied", "probe", "load"
            ]),
            "unclosed": keys(&["hardware::read"]),
            "derived": keys(&["Slot::clone", "Slot::eq"]),
            "unconstrained": [
                "core::option::{impl core::ops::try_trait::Try for core::option::Option<T>}::branch",
                "core::option::{impl core::ops::try_trait::FromResidual<core::option::Option<!>> for core::option::Option<T>}::from_residual",
                "core::sync::atomic::{core::sync::atomic::Atomic<u32, core::sync::atomic::private::Align4<u32>>}::load",
                "core::sync::atomic::Atomic",
                "core::sync::atomic::private::Align4"
            ]
        })
    }

    /// The problems of the registration check of the registration module
    /// for what `edit` makes of [`registration`].
    fn registration_problems(edit: impl FnOnce(&mut Value)) -> Vec<String> {
        let mut fields = registration();
        edit(&mut fields);
        let extraction = extraction("Registration", REGISTRATION);
        classify(&target(fields), &extraction, PACKAGE, &crate_inventory()).0
    }

    /// Removes `key` from the list `list` of `fields`.
    fn remove(fields: &mut Value, list: &str, key: &str) {
        let entries = fields[list].as_array_mut().expect("a list");
        let before = entries.len();
        entries.retain(|entry| entry != key);
        assert_eq!(entries.len() + 1, before, "{key} is not in {list}");
    }

    #[test]
    fn default_and_derived_methods_are_classified() {
        let registered = extraction("Registration", REGISTRATION);
        let (problems, found) = classify(
            &target(registration()),
            &registered,
            PACKAGE,
            &crate_inventory(),
        );
        assert_eq!(problems, Vec::<String>::new());
        assert_eq!(
            found.transparent,
            keys(&[
                "Slot::clone",
                "Slot::eq",
                "Slots::bump",
                "Slots::value",
                "Table::total",
                "copied",
                "load",
                "probe",
                "same"
            ])
        );
        assert_eq!(found.opaque, keys(&["hardware::read"]));
        let unconstrained = registration()["unconstrained"].clone();
        let mut external: Vec<String> = serde_json::from_value(unconstrained).expect("names");
        external.sort();
        assert_eq!(found.external, external);

        // The derived `eq` of `Wrapper` and the hand-written `eq` of its
        // `PartialEq<u32>` have the same key. With the hand-written `eq` left
        // out of the inventory, the key is that of the derived method alone,
        // to which both names map, and a derived entry refuses it.
        let proved = names_proved();
        let eq = format!("{NAMES_FILE}#Wrapper::eq");
        let mut inventory = crate_inventory();
        assert!(inventory.functions.remove(&eq), "{eq}");
        let check = |fields: Value, translation: &str| {
            let extraction = extraction("Names", translation);
            classify(&target(fields), &extraction, PACKAGE, &inventory)
        };
        let derived = json!({"proves": proved, "derived": [eq]});
        let expected = format!(
            "reg: derived entry {eq} is reached under several Rust names: \
             registration_fixture::names::{{impl core::cmp::PartialEq<registration_fixture::names::Wrapper<T>> for registration_fixture::names::Wrapper<T>}}::eq, \
             registration_fixture::names::{{impl core::cmp::PartialEq<u32> for registration_fixture::names::Wrapper<u32>}}::eq"
        );
        let (problems, found) = check(derived.clone(), NAMES);
        assert_eq!(problems, std::slice::from_ref(&expected));
        let mut keys = [proved.clone(), vec![eq.clone()]].concat();
        keys.sort();
        assert_eq!(found.transparent, keys);
        // The same with the hand-written `eq` cut: the change of the captured
        // translation makes its entry opaque, with the Lean name without the
        // namespace and the file of declarations that the pinned Aeneas
        // writes for a cut local item.
        let mut translation: Value = serde_json::from_str(NAMES).expect("a translation");
        let hand_written = "registration_fixture::names::{impl core::cmp::PartialEq<u32> for registration_fixture::names::Wrapper<u32>}::eq";
        let functions = translation["functions"]
            .as_array_mut()
            .expect("the functions");
        let entry = (functions.iter_mut())
            .find(|entry| entry["rust_name"] == hand_written)
            .expect("the hand-written eq");
        entry["is_opaque"] = json!(true);
        entry["lean_name"] = json!("names.WrapperU32.Insts.CoreCmpPartialEqU32.eq");
        entry["lean_file"] = json!("KrepiGen/Reg/Names/FunsExternal_Template.lean");
        let (problems, found) = check(derived, &translation.to_string());
        assert_eq!(problems, [expected]);
        assert_eq!(found.opaque, [eq]);
    }

    #[test]
    fn a_key_of_a_function_and_a_derived_method_is_not_registered() {
        // The derived `eq` of `Wrapper` and the hand-written `eq` of its
        // `PartialEq<u32>` have one key, which the inventory holds as a
        // function and as a derived method: under `proves`, the
        // hand-written `eq` would stand for the derived one.
        let eq = format!("{NAMES_FILE}#Wrapper::eq");
        let inventory = crate_inventory();
        assert!(inventory.functions.contains(&eq) && inventory.derived.contains(&eq));
        let proved = [names_proved(), vec![eq.clone()]].concat();
        let extraction = extraction("Names", NAMES);
        let fields = json!({"proves": proved});
        let (problems, found) = classify(&target(fields), &extraction, PACKAGE, &inventory);
        let refused = |rust_name: &str, lean_name: &str| {
            format!(
                "reg: reached local function {rust_name} ({lean_name}) is not registered: it maps to {eq}, the key of both a function and a derived method in {NAMES_FILE}, which the key does not tell apart"
            )
        };
        assert_eq!(
            problems,
            [
                refused(
                    "registration_fixture::names::{impl core::cmp::PartialEq<registration_fixture::names::Wrapper<T>> for registration_fixture::names::Wrapper<T>}::eq",
                    "KrepiGen.Reg.Names.names.Wrapper.Insts.CoreCmpPartialEqWrapper.eq"
                ),
                refused(
                    "registration_fixture::names::{impl core::cmp::PartialEq<u32> for registration_fixture::names::Wrapper<u32>}::eq",
                    "KrepiGen.Reg.Names.names.WrapperU32.Insts.CoreCmpPartialEqU32.eq"
                ),
                format!("reg: proved function {eq} is not translated by this extraction"),
            ]
        );
        assert_eq!(found.transparent, names_proved());
    }

    #[test]
    fn a_reached_local_function_that_is_not_registered_fails() {
        let problems =
            registration_problems(|fields| remove(fields, "proves", &keys(&["load"])[0]));
        assert_eq!(
            problems,
            [format!(
                "reg: reached local function {FILE}#load is neither proved nor registered as unclosed"
            )]
        );
    }

    #[test]
    fn a_cut_local_item_outside_unclosed_fails() {
        let key = &keys(&["hardware::read"])[0];
        let problems = registration_problems(|fields| remove(fields, "unclosed", key));
        assert_eq!(
            problems,
            [format!(
                "reg: opaque local item {key} must be registered as unclosed"
            )]
        );
    }

    #[test]
    fn a_reached_external_item_that_is_not_registered_fails() {
        let item = "core::sync::atomic::Atomic";
        let problems = registration_problems(|fields| remove(fields, "unconstrained", item));
        assert_eq!(
            problems,
            [format!("reg: external item {item} is not registered")]
        );
    }

    #[test]
    fn a_registered_external_item_that_is_not_reached_fails() {
        let item = "core::sync::atomic::{core::sync::atomic::Atomic<u64, core::sync::atomic::private::Align8<u64>>}::load";
        let problems = registration_problems(|fields| {
            let entries = fields["unconstrained"].as_array_mut().expect("a list");
            entries.push(json!(item));
        });
        assert_eq!(
            problems,
            [format!(
                "reg: registered external item {item} is not reached"
            )]
        );
    }

    #[test]
    fn a_registered_entry_that_is_not_reached_fails() {
        // Functions of the inventory that the extraction does not reach.
        let scan = "kernel/src/scan.rs#take";
        let closure = "kernel/src/closure.rs#owner";
        let derived = "kernel/src/registration.rs#Slot::fmt";
        let problems = registration_problems(|fields| {
            (fields["proves"].as_array_mut().expect("a list")).push(json!(scan));
            (fields["unclosed"].as_array_mut().expect("a list")).push(json!(closure));
            (fields["derived"].as_array_mut().expect("a list")).push(json!(derived));
        });
        assert_eq!(
            problems,
            [
                format!("reg: proved function {scan} is not translated by this extraction"),
                format!("reg: unclosed entry {closure} is not reached by this extraction"),
                format!("reg: derived entry {derived} is not reached by this extraction"),
            ]
        );
    }

    #[test]
    fn a_derived_entry_that_is_no_derived_method_fails() {
        let key = &keys(&["same"])[0];
        let problems = registration_problems(|fields| {
            remove(fields, "proves", key);
            (fields["derived"].as_array_mut().expect("a list")).push(json!(key));
        });
        assert_eq!(
            problems,
            [format!(
                "reg: derived entry {key} is reached as registration_fixture::registration::same, which is not a derived method"
            )]
        );
    }

    #[test]
    fn the_body_of_a_closure_maps_to_no_key_and_is_not_registered() {
        let fields = json!({"proves": [
            "kernel/src/closure.rs#index_of", "kernel/src/closure.rs#owner"
        ]});
        let extraction = extraction("Closure", CLOSURE);
        let (problems, found) = classify(&target(fields), &extraction, PACKAGE, &crate_inventory());
        assert_eq!(
            problems,
            [
                "reg: reached local function registration_fixture::closure::owner::{impl core::ops::function::FnOnce<(registration_fixture::closure::Error,), registration_fixture::closure::Error> for registration_fixture::closure::owner::{closure}}::call_once (KrepiGen.Reg.Closure.closure.owner.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once) is not registered: the body of a closure has no inventory key, so a target can neither prove nor register it; write the code without the closure, as the rule on closures as callbacks (R4) of the provable subset says"
            ]
        );
        assert_eq!(
            found.transparent,
            [
                "kernel/src/closure.rs#index_of",
                "kernel/src/closure.rs#owner"
            ]
        );
    }

    #[test]
    fn a_loop_in_the_file_of_a_macro_maps_to_no_key_and_is_not_registered() {
        let fields = json!({"proves": [
            "kernel/src/scan.rs#take", "kernel/src/scan.rs#compare", "kernel/src/scan.rs#halve"
        ]});
        // The pinned tools place the loop of this `matches!` condition in
        // the file of its function.
        let extraction = extraction("Scan", SCAN);
        let inventory = crate_inventory();
        let (problems, _) = classify(&target(fields.clone()), &extraction, PACKAGE, &inventory);
        assert_eq!(problems, Vec::<String>::new());
        // Placed in the file of the macro, as earlier tools placed it, the
        // loop and its body have no key.
        let mut translation: Value = serde_json::from_str(SCAN).expect("a translation");
        let macros = "/rustc/library/core/src/macros/mod.rs";
        for entry in translation["functions"]
            .as_array_mut()
            .expect("the functions")
        {
            if entry.get("loop").is_some() {
                entry["source"]["file"] = json!(macros);
            }
        }
        let moved = extraction_of("Scan", &translation);
        let (problems, _) = classify(&target(fields), &moved, PACKAGE, &inventory);
        let problem = |lean: &str| {
            format!(
                "reg: reached local function registration_fixture::scan::halve (KrepiGen.Reg.Scan.scan.{lean}) is not registered: the tools place it in {macros}, which is no production file of the package, so it has no inventory key; a loop condition calls a function rather than a macro, as the loop shapes of the provable subset say"
            )
        };
        assert_eq!(
            problems,
            [problem("halve_loop.body"), problem("halve_loop")]
        );
    }

    /// The extraction of `module` whose translation is `translation`.
    fn extraction_of(module: &str, translation: &Value) -> Extraction {
        extraction(module, &translation.to_string())
    }

    #[test]
    fn names_that_do_not_tell_functions_apart_are_not_registered() {
        let mut inventory = crate_inventory();
        let key = format!("{FILE}#Slots::value");
        inventory.functions.insert(format!("{key}#2"));
        let rust_name = "registration_fixture::registration::{impl registration_fixture::registration::Table for registration_fixture::registration::Slots}::value";
        assert_eq!(
            key_of(PACKAGE, "src/registration.rs", rust_name, "", &inventory),
            Err(format!(
                "it maps to {key}, the key of more than one method of trait implementations in {FILE}, which its name does not tell apart"
            ))
        );
        // A function in a body, which the inventory does not count.
        assert_eq!(
            key_of(
                PACKAGE,
                "src/registration.rs",
                "registration_fixture::registration::probe::inner",
                "",
                &inventory
            ),
            Err(format!(
                "it maps to {FILE}#probe::inner, not to exactly one function of the inventory"
            ))
        );
        // A name below another module than that of its file.
        assert_eq!(
            key_of(
                PACKAGE,
                "src/registration.rs",
                "registration_fixture::scan::take",
                "",
                &inventory
            ),
            Err(format!("its name is not below the module of {FILE}"))
        );
        // A source outside the package.
        assert!(
            key_of(
                PACKAGE,
                "../user/src/lib.rs",
                "registration_fixture::f",
                "",
                &inventory
            )
            .is_err()
        );
    }

    #[test]
    fn derived_names_are_recognised() {
        // The names that the pinned Aeneas writes.
        let functions = &extraction("Registration", REGISTRATION)
            .translation
            .functions;
        let derived: Vec<&str> = (functions.iter())
            .map(|entry| entry.rust_name.as_str())
            .filter(|name| is_derived_name(name))
            .collect();
        assert_eq!(
            derived,
            [
                "registration_fixture::registration::{impl core::clone::Clone for registration_fixture::registration::Slot}::clone",
                "registration_fixture::registration::{impl core::cmp::PartialEq<registration_fixture::registration::Slot> for registration_fixture::registration::Slot}::eq"
            ]
        );
        for name in [
            "registration_fixture::registration::{impl core::clone::Clone for registration_fixture::registration::Slot}::clone_from",
            "registration_fixture::registration::{impl core::fmt::Display for registration_fixture::registration::Slot}::fmt",
            "registration_fixture::registration::{impl registration_fixture::registration::Table for registration_fixture::registration::Slot}::clone",
            "registration_fixture::registration::Slot::clone",
        ] {
            assert!(!is_derived_name(name), "{name}");
        }
    }

    #[test]
    fn aeneas_names_map_to_keys() {
        let key = |rust_name: &str, module: &str| {
            key_for_rust_name(FILE, rust_name, "registration_fixture", module)
        };
        for (rust_name, expected) in [
            (
                "registration_fixture::registration::{registration_fixture::registration::Slots}::bump",
                "Slots::bump",
            ),
            (
                "registration_fixture::registration::{impl registration_fixture::registration::Table for registration_fixture::registration::Slots}::value",
                "Slots::value",
            ),
            (
                "registration_fixture::registration::{impl core::cmp::PartialEq<registration_fixture::registration::Slot> for registration_fixture::registration::Slot}::eq",
                "Slot::eq",
            ),
            ("registration_fixture::registration::same", "same"),
            (
                "registration_fixture::registration::hardware::read",
                "hardware::read",
            ),
        ] {
            assert_eq!(
                key(rust_name, "registration"),
                Some(format!("{FILE}#{expected}")),
                "{rust_name}"
            );
        }
        // The methods of a generic type: an inherent one, one of a local
        // trait and one of an implementation for an instance of the type.
        for (rust_name, expected) in [
            (
                "registration_fixture::names::{registration_fixture::names::Wrapper<T>}::get",
                "Wrapper::get",
            ),
            (
                "registration_fixture::names::{impl registration_fixture::names::Count for registration_fixture::names::Wrapper<T>}::count",
                "Wrapper::count",
            ),
            (
                "registration_fixture::names::{impl core::cmp::PartialEq<u32> for registration_fixture::names::Wrapper<u32>}::eq",
                "Wrapper::eq",
            ),
        ] {
            assert_eq!(
                key_for_rust_name(NAMES_FILE, rust_name, "registration_fixture", "names"),
                Some(format!("{NAMES_FILE}#{expected}")),
                "{rust_name}"
            );
        }
        // At the root of the crate, the module is empty; a name below
        // another module has no key in the file.
        assert_eq!(
            key("registration_fixture::registration::same", ""),
            Some(format!("{FILE}#registration::same"))
        );
        assert_eq!(
            key("registration_fixture::closure::owner", "registration"),
            None
        );
        assert_eq!(key("other_crate::registration::same", "registration"), None);
        // The keys are those of the inventory.
        let inventory = crate_inventory();
        for (file, module, namespace, text) in [
            (FILE, "registration", "Registration", REGISTRATION),
            (NAMES_FILE, "names", "Names", NAMES),
        ] {
            let functions = &extraction(namespace, text).translation.functions;
            for entry in functions.iter().filter(|entry| entry.is_local) {
                let found = key_for_translated(
                    file,
                    &entry.rust_name,
                    &entry.lean_name,
                    "registration_fixture",
                    module,
                )
                .expect("a key");
                let known =
                    inventory.functions.contains(&found) || inventory.derived.contains(&found);
                assert!(known, "{found}");
            }
        }
    }

    #[test]
    fn default_methods_map_to_the_scanned_key() {
        let inventory = crate_inventory();
        // Default methods, one with a loop and one with two, a default
        // method named `default` and a free function of that name with its
        // loop: the Lean names that the pinned Aeneas gives them map to the
        // key of the inventory.
        let cases: [(&str, &str, &str, &[&str]); 4] = [
            (
                REGISTRATION,
                "registration",
                "Table::total",
                &[
                    "Table.total.default_loop.body",
                    "Table.total.default_loop",
                    "Table.total.default",
                ],
            ),
            (
                NAMES,
                "names",
                "Count::twice",
                &[
                    "Count.twice.default_loop0.body",
                    "Count.twice.default_loop0",
                    "Count.twice.default_loop1.body",
                    "Count.twice.default_loop1",
                    "Count.twice.default",
                ],
            ),
            (NAMES, "names", "Count::default", &["Count.default.default"]),
            (
                NAMES,
                "names",
                "default",
                &["default_loop.body", "default_loop", "default"],
            ),
        ];
        for (text, module, name, leans) in cases {
            let file = format!("kernel/src/{module}.rs");
            let rust_name = format!("registration_fixture::{module}::{name}");
            let namespace = match module {
                "registration" => "Registration",
                _ => "Names",
            };
            let prefix = format!("KrepiGen.Reg.{namespace}.{module}.");
            let functions = &extraction(namespace, text).translation.functions;
            let captured: Vec<&str> = (functions.iter())
                .filter(|entry| entry.rust_name == rust_name)
                .map(|entry| {
                    entry
                        .lean_name
                        .strip_prefix(&prefix)
                        .expect("the namespace")
                })
                .collect();
            assert_eq!(captured, leans, "{rust_name}");
            let key = format!("{file}#{name}");
            assert!(inventory.functions.contains(&key), "{key}");
            let method = name.rsplit("::").next().expect("a name");
            for lean in leans {
                let lean = format!("{prefix}{lean}");
                // Only the definitions of a default method and its loops
                // read as one.
                assert_eq!(
                    is_default_method(method, &lean),
                    name.contains("::"),
                    "{lean}"
                );
                assert_eq!(
                    key_for_translated(&file, &rust_name, &lean, "registration_fixture", module),
                    Some(key.clone()),
                    "{lean}"
                );
            }
        }
        // Implementations, free functions and loop bodies keep their keys.
        for (rust_name, lean, expected) in [
            (
                "registration_fixture::registration::{impl registration_fixture::registration::Table for registration_fixture::registration::Slots}::value",
                "KrepiGen.Reg.Registration.registration.Slots.Insts.Registration_fixtureRegistrationTable.value",
                "Slots::value",
            ),
            (
                "registration_fixture::closure::index_of",
                "KrepiGen.Reg.Closure.closure.index_of_loop.body",
                "index_of",
            ),
        ] {
            let file = if expected == "index_of" {
                "kernel/src/closure.rs"
            } else {
                FILE
            };
            let module = if expected == "index_of" {
                "closure"
            } else {
                "registration"
            };
            assert_eq!(
                key_for_translated(file, rust_name, lean, "registration_fixture", module),
                Some(format!("{file}#{expected}"))
            );
        }
        // A loop index must be a number: the captured `default_loop1` with
        // a letter for its index, which the tools do not write, is no loop
        // of the default method.
        assert!(!is_default_method(
            "twice",
            "KrepiGen.Reg.Names.names.Count.twice.default_loopx"
        ));
    }

    #[test]
    fn derived_entries_need_a_derive_and_no_source() {
        let inventory = crate_inventory();
        let derived =
            |entries: &[&str]| derived_problems(&target(json!({"derived": entries})), &inventory);
        assert_eq!(
            derived(&[&format!("{FILE}#Slot::clone"), &format!("{FILE}#Slot::eq")]),
            Vec::<String>::new()
        );
        assert_eq!(
            derived(&[
                &format!("{FILE}#same"),
                "Slot::clone",
                &format!("{FILE}#Slot::hash")
            ]),
            [
                format!("target reg: derived entry {FILE}#same is a production function"),
                "target reg: derived entry Slot::clone is not a key `file#Type::method`"
                    .to_string(),
                format!(
                    "target reg: derived entry {FILE}#Slot::hash matches no #[derive] attribute in {FILE}"
                ),
            ]
        );
    }
}
