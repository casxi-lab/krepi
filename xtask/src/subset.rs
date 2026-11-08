//! The `subset` step of `cargo xtask check`: the mechanical checks that
//! "Mechanical checks" in `docs/conventions/provable-subset.md` states.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use serde::Deserialize;
use syn::buffer::{Cursor, TokenBuffer};
use syn::ext::IdentExt;
use syn::visit::{self, Visit};
use syn::{Attribute, Ident, UseTree};

use crate::check::{self, Facts};
use crate::formal::inventory;
use crate::manifests::{self, KERNEL};
use crate::repo::{self, Entry, Tree};

/// The interior-mutability types by name, and the `core` modules of others.
const CELLS: [&str; 4] = ["Cell", "RefCell", "UnsafeCell", "OnceCell"];
const MODULES: [&str; 2] = ["cell", "atomic"];

/// The files that the `paths` blocks of the `Extractability` sections of the
/// contracts in `tree` list, and each line that names no tracked `.rs` file.
pub fn listed(tree: &Tree) -> (BTreeSet<String>, Vec<String>) {
    let rust = Vec::from_iter(tree.entries().map(|e| e.0).filter(|p| p.ends_with(".rs")));
    let (mut files, mut problems) = (BTreeSet::new(), Vec::new());
    for (path, text) in tree.texts() {
        let parts: Vec<&str> = path.split('/').collect();
        let contract = matches!(parts[..], ["docs", "domains", _, _, "contract.md"]);
        let (mut section, mut block) = (false, false);
        for line in text.lines().map(str::trim_end).filter(|_| contract) {
            let info = line.trim_start().trim_start_matches(['`', '~']);
            let fence = line.trim_start().len() >= info.len() + 3;
            match line.trim_start().strip_prefix("## ") {
                _ if block && !(fence && info.is_empty()) => {
                    let named = rust.iter().filter(|file| repo::is_within(file, line));
                    let none = format!("{path}: {line:?} names no tracked .rs file");
                    problems.extend((named.clone().count() == 0).then_some(none));
                    files.extend(named.map(|file| file.to_string()));
                }
                Some(title) => section = title.trim() == "Extractability",
                None => block = fence && !block && section && info.trim() == "paths",
            }
        }
    }
    (files, problems)
}

/// The problems of one file, each with its line.
struct Scan(Vec<(usize, String)>);

/// Whether `ident`, without `r#`, is one of the lists of `names`.
fn is(ident: &Ident, names: &[&[&str]]) -> bool {
    (names.concat()).contains(&ident.unraw().to_string().as_str())
}

/// Whether a macro holds, at `at`, a name of [`CELLS`] or [`MODULES`], `cfg`
/// or `static`.
fn held(at: Cursor) -> bool {
    (at.ident()).is_some_and(|(ident, _)| is(&ident, &[&CELLS, &MODULES, &["cfg", "static"]]))
}

impl<'ast> Visit<'ast> for Scan {
    fn visit_attribute(&mut self, attr: &'ast Attribute) {
        if (attr.path().segments.last()).is_some_and(|last| is(&last.ident, &[&["cfg"]])) {
            let what = "cfg outside the allowlist".to_string();
            self.0.push((attr.pound_token.span.start().line, what));
        }
        visit::visit_attribute(self, attr);
    }
    // The allowlist: `#[cfg(test)]` in exactly this form on a module, whose
    // content is test code; the module's other attributes are checked.
    fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
        let allowed = |attr: &&Attribute| inventory::is_test(std::slice::from_ref(*attr));
        if !item.attrs.iter().any(|attr| allowed(&attr)) {
            return visit::visit_item_mod(self, item);
        }
        (item.attrs.iter().filter(|attr| !allowed(attr))).for_each(|a| self.visit_attribute(a));
    }
    fn visit_static_mutability(&mut self, mutability: &'ast syn::StaticMutability) {
        if let syn::StaticMutability::Mut(token) = mutability {
            self.0.push((token.span.start().line, "static mut".into()));
        }
    }
    fn visit_path(&mut self, path: &'ast syn::Path) {
        let words = Vec::from_iter(path.segments.iter().map(|s| s.ident.unraw().to_string()));
        let module = (words.windows(2)).any(|pair| MODULES.contains(&pair[0].as_str()));
        if module || words.iter().any(|word| CELLS.contains(&word.as_str())) {
            let what = format!("interior mutability: {}", words.join("::"));
            (self.0).push((path.segments[0].ident.span().start().line, what));
        }
        visit::visit_path(self, path);
    }
    // A module of `MODULES` in a use tree is followed by more or imported.
    fn visit_use_tree(&mut self, tree: &'ast UseTree) {
        let ident = match tree {
            UseTree::Path(tree) => &tree.ident,
            UseTree::Name(tree) => &tree.ident,
            UseTree::Rename(tree) => &tree.ident,
            _ => return visit::visit_use_tree(self, tree),
        };
        if !is(ident, &[&CELLS, &MODULES]) {
            return visit::visit_use_tree(self, tree);
        }
        let what = format!("interior mutability: use of {ident}");
        self.0.push((ident.span().start().line, what));
    }
    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        let tokens = TokenBuffer::new2(mac.tokens.clone());
        if inventory::finds(tokens.begin(), held) {
            let what = "a macro holds a refused name".to_string();
            self.0.push((mac.bang_token.spans[0].start().line, what));
        }
        visit::visit_macro(self, mac);
    }
}

/// The problems of the files that the contracts in `tree` list, apart from
/// those that the inventory reaches only as tests from the `roots` of the
/// kernel targets, each `<path>:<line>: <what>`, and the number of files.
pub fn check(tree: &Tree, roots: &[(String, bool)]) -> (usize, Vec<String>) {
    let (files, mut problems) = listed(tree);
    let reached = inventory::inventory(tree, roots, KERNEL).0.reached;
    let files = Vec::from_iter(files.iter().filter(|f| reached.get(*f) != Some(&false)));
    for file in &files {
        let text = (tree.text(file)).ok_or("not a UTF-8 regular file".to_string());
        let parse = |text| syn::parse_file(text).map_err(|e| format!("does not parse: {e}"));
        let mut scan = Scan(Vec::new());
        let parsed = text.and_then(parse).map(|parsed| scan.visit_file(&parsed));
        problems.extend(parsed.err().map(|error| format!("{file}: {error}")));
        problems.extend((scan.0.iter()).map(|(line, what)| format!("{file}:{line}: {what}")));
    }
    (files.len(), problems)
}

/// A compile-fail case: replacing `find`, once in the file `file` of the
/// workspace, by `replace` makes its build fail with the error code `error`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Case {
    pub file: String,
    pub find: String,
    pub replace: String,
    pub error: String,
}

/// Writes the tracked entries of the workspace `ws` of `tree` below `work`,
/// with `case` applied.
fn copy(tree: &Tree, ws: &str, case: Option<&Case>, work: &Path) -> Result<(), String> {
    for (path, entry) in tree.entries().filter(|(path, _)| repo::is_within(path, ws)) {
        let to = work.join(path);
        let made = fs::create_dir_all(to.parent().expect("a path below the copy"));
        let written = made.and_then(|()| match entry {
            Entry::File(bytes) => fs::write(&to, bytes),
            Entry::Symlink(target) => std::os::unix::fs::symlink(target, &to),
            Entry::Submodule => Ok(()),
        });
        written.map_err(|error| format!("{}: {error}", to.display()))?;
    }
    let Some(case) = case else { return Ok(()) };
    let text = (tree.text(&case.file)).filter(|_| repo::is_within(&case.file, ws));
    let text = text.ok_or(format!("{} is no tracked UTF-8 file of {ws}", case.file))?;
    let found = (text.char_indices()).filter(|(at, _)| text[*at..].starts_with(&case.find));
    let edited = text.replacen(&case.find, &case.replace, 1);
    match found.count() {
        1 => fs::write(work.join(&case.file), edited).map_err(|error| error.to_string()),
        count => Err(format!("find occurs {count} times in {}", case.file)),
    }
}

/// Builds the workspace `ws` of `tree`, with `case` applied, by `cargo check`
/// in a copy at `work` that it removes; the build must succeed without a
/// case, and with one fail with a diagnostic of the case's error code.
pub fn build(tree: &Tree, ws: &str, case: Option<&Case>, work: &Path) -> Result<(), String> {
    let _ = fs::remove_dir_all(work);
    let output = copy(tree, ws, case, work).and_then(|()| {
        let args = "check --locked --offline --color never --workspace --manifest-path".split(' ');
        let mut cargo = std::process::Command::new(check::cargo());
        let command = (cargo.args(args).arg(format!("{ws}/Cargo.toml"))).current_dir(work);
        (command.output()).map_err(|error| format!("cannot run cargo: {error}"))
    });
    let _ = fs::remove_dir_all(work);
    let output = output?;
    let stderr = String::from_utf8_lossy(&output.stderr);
    let want = case.map(|case| format!("error[{}]", case.error));
    let reported = (want.as_ref()).is_some_and(|w| (stderr.lines()).any(|l| l.starts_with(w)));
    match (want, output.status.success()) {
        (None, false) => Err(format!("the build fails:\n{stderr}")),
        (Some(_), true) => Err("the build succeeds".to_string()),
        (Some(want), _) if !reported => Err(format!("the build fails without {want}:\n{stderr}")),
        _ => Ok(()),
    }
}

/// The `subset` step in `root`: the listed files, the unchanged kernel
/// workspace, and each case, a TOML file in a `compile-fail` directory in it.
pub fn run(root: &Path, facts: &mut Facts) -> Result<(), String> {
    let tree = Tree::load(root)?;
    let metadata = || manifests::kernel_metadata(root).and_then(|m| inventory::roots(&m, KERNEL));
    let roots = (!listed(&tree).0.is_empty()).then(metadata).transpose()?;
    let (files, mut problems) = check(&tree, &roots.unwrap_or_default());
    let case = |p: &&str| p.ends_with(".toml") && repo::parent(p).ends_with("/compile-fail");
    let paths = tree.entries().map(|(path, _)| path);
    let cases = Vec::from_iter(paths.filter(|p| repo::is_within(p, KERNEL)).filter(case));
    let work = root.join(format!("artifacts/subset/{}", std::process::id()));
    let base = (!cases.is_empty()).then(|| build(&tree, KERNEL, None, &work.join("base")));
    problems.extend(base.and_then(Result::err).map(|e| format!("{KERNEL}: {e}")));
    for (number, path) in cases.iter().enumerate() {
        let text = (tree.text(path)).ok_or("not a UTF-8 regular file".to_string());
        let case = text.and_then(|text| toml::from_str(text).map_err(|e| e.to_string()));
        let ran = case.and_then(|c| build(&tree, KERNEL, Some(&c), &work.join(number.to_string())));
        problems.extend(ran.err().map(|error| format!("{path}: {error}")));
    }
    let _ = fs::remove_dir_all(&work);
    println!("subset: {files} files, {} compile-fail cases", cases.len());
    facts.push(("files".to_string(), files.to_string()));
    facts.push(("compile-fail cases".to_string(), cases.len().to_string()));
    problems.is_empty().then_some(()).ok_or(problems.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The contract of the fixture component, and the root of the crate
    /// that it lists.
    const CONTRACT: &str = "docs/domains/d/c/contract.md";
    const FILE: &str = "kernel/x/src/a.rs";

    /// A contract whose `Extractability` section lists `paths` in a block
    /// between a block of another kind and the next section.
    fn contract(paths: &[&str]) -> String {
        format!(
            "# C\n\n## Terms\n\n```paths\nkernel/elsewhere.rs\n```\n\n## Extractability\n\n\
             The component follows the subset:\n\n```rust\nkernel/absent.rs\n```\n\n\
             ```paths\n{}\n```\n\n## Check and execute\n\n```paths\nkernel/after.rs\n```\n",
            paths.join("\n")
        )
    }

    /// The tree of `files` with the contract that lists `paths`.
    fn tree(paths: &[&str], files: &[(&str, &str)]) -> Tree {
        let contract = contract(paths);
        Tree::from_files(&[&[(CONTRACT, contract.as_str())], files].concat())
    }

    /// The problems of [`FILE`], listed and the root of its crate, with the
    /// text `text`.
    fn problems(text: &str) -> Vec<String> {
        let (files, problems) = check(&tree(&[FILE], &[(FILE, text)]), &[(FILE.into(), true)]);
        assert_eq!(files, 1);
        problems
    }

    /// The problem `what` at `line` of [`FILE`].
    fn at(line: usize, what: &str) -> Vec<String> {
        vec![format!("{FILE}:{line}: {what}")]
    }

    #[test]
    fn a_static_mut_in_a_listed_file_fails() {
        let text = "pub static A: u32 = 0;\nstatic mut B: u32 = 0;\n";
        assert_eq!(problems(text), at(2, "static mut"));
        // In a function body, in an initializer and in an extern block.
        let body = "pub fn f() -> u8 {\n    static mut C: u8 = 0;\n    0\n}\n";
        assert_eq!(problems(body), at(2, "static mut"));
        let initializer = "pub const D: () = {\n    static mut E: u8 = 0;\n};\n";
        assert_eq!(problems(initializer), at(2, "static mut"));
        let foreign = "unsafe extern \"C\" {\n    static mut F: u8;\n}\n";
        assert_eq!(problems(foreign), at(2, "static mut"));
        // The same text in a file that no contract lists.
        let listed = "kernel/x/src/b.rs";
        let tree = tree(&[listed], &[(FILE, text), (listed, "pub fn b() {}\n")]);
        assert_eq!(check(&tree, &[(FILE.into(), true)]), (1, Vec::new()));
    }

    #[test]
    fn each_interior_mutability_type_in_a_listed_file_fails() {
        let types = ["Cell", "RefCell", "UnsafeCell", "OnceCell"];
        for ty in types.iter().map(|ty| format!("{ty}<u64>")) {
            let path = &ty[..ty.len() - 5];
            let what = format!("interior mutability: {path}");
            assert_eq!(
                problems(&format!("pub struct L {{ c: {ty} }}\n")),
                at(1, &what)
            );
        }
        let atomic = "core::sync::atomic::AtomicUsize";
        let what = format!("interior mutability: {atomic}");
        assert_eq!(
            problems(&format!("pub struct L {{ c: {atomic} }}\n")),
            at(1, &what)
        );
        // Imports, a module that is imported, and a glob.
        for (text, word) in [
            ("use core::sync::atomic::AtomicU8;\n", "atomic"),
            ("use core::{cell::*};\n", "cell"),
            ("use core::cell::Cell as Plain;\n", "cell"),
            ("use core::sync::{Exclusive, atomic};\n", "atomic"),
        ] {
            let what = format!("interior mutability: use of {word}");
            assert_eq!(problems(text), at(1, &what), "{text}");
        }
        let module = "use core::cell;\npub fn f(x: &cell::LazyCell<u8>) {}\n";
        let mut expected = at(1, "interior mutability: use of cell");
        expected.extend(at(2, "interior mutability: cell::LazyCell"));
        assert_eq!(problems(module), expected);
        // A raw name, a path in an expression and a type argument.
        let more = "pub fn g() {\n    let _ = r#RefCell::new(1);\n    \
                    let _: Option<core::cell::Ref<u8>> = None;\n}\n";
        let mut expected = at(2, "interior mutability: RefCell::new");
        expected.extend(at(3, "interior mutability: core::cell::Ref"));
        assert_eq!(problems(more), expected);
        // A variable and a function named `cell`.
        let named = "pub fn cell(cell: u8) -> u8 {\n    let atomic = cell + 1;\n    atomic\n}\n\
                     pub fn h() -> u8 {\n    self::cell(1)\n}\n";
        assert_eq!(problems(named), Vec::<String>::new());
    }

    #[test]
    fn a_cfg_attribute_outside_the_allowlist_fails() {
        let outside = "cfg outside the allowlist";
        assert_eq!(
            problems("#[cfg(feature = \"x\")] pub fn f() {}\n"),
            at(1, outside)
        );
        for (text, line) in [
            ("#[cfg(test)]\nfn t() {}\n", 1),
            ("#[cfg(all(test))]\nmod t {}\n", 1),
            ("#![cfg(x)]\n", 1),
            ("pub struct S {\n    #[cfg(x)]\n    f: u8,\n}\n", 2),
            ("pub fn f() {\n    #[cfg(x)]\n    let _a = 1;\n}\n", 2),
            ("#[cfg(test)]\n#[cfg(x)]\nmod t {}\n", 2),
            ("#[core::cfg(x)]\npub fn f() {}\n", 1),
        ] {
            assert_eq!(problems(text), at(line, outside), "{text}");
        }
        // The allowlist: `#[cfg(test)]` on a module, whose content is test
        // code, inline or in its own file.
        let tests = "pub fn f() {}\n\n#[cfg(test)]\nmod tests {\n    \
                     use core::cell::RefCell;\n    static mut T: u8 = 0;\n    \
                     #[cfg(x)]\n    fn t() {}\n}\n\n#[cfg(test)]\nmod more;\n";
        let more = ("kernel/x/src/more.rs", "static mut M: u8 = 0;\n");
        let tree = tree(&["kernel/x/src"], &[(FILE, tests), more]);
        assert_eq!(check(&tree, &[(FILE.into(), true)]), (1, Vec::new()));
        // Without the roots, the file of the test module is checked.
        let (files, problems) = check(&tree, &[]);
        assert_eq!(
            (files, problems),
            (2, vec!["kernel/x/src/more.rs:1: static mut".into()])
        );
    }

    #[test]
    fn a_macro_that_holds_a_refused_name_fails() {
        let held = "a macro holds a refused name";
        for (text, line) in [
            (
                "macro_rules! m {\n    () => { static mut X: u8 = 0; };\n}\n",
                1,
            ),
            ("pub fn f() {\n    let _ = m!(Cell);\n}\n", 2),
            (
                "pub fn f() {\n    m!(core::sync::atomic::AtomicU8);\n}\n",
                2,
            ),
            ("pub fn f() -> bool {\n    m!(cfg!(test))\n}\n", 2),
            ("pub fn f() {\n    m!(atomic);\n}\n", 2),
            // `static` and `mut` apart, which a macro joins to `static mut`,
            // and `static` alone, in a lifetime as well.
            ("state!(static, mut);\n", 1),
            (
                "macro_rules! state {\n    ($m:tt) => { pub static $m X: u8 = 0; };\n}\n",
                1,
            ),
            ("pub fn f() {\n    m!(&'static str);\n}\n", 2),
        ] {
            assert_eq!(problems(text), at(line, held), "{text}");
        }
        // `cfg!` itself and `cfg_attr` are left to review, and a `static`
        // item without `mut` outside a macro passes.
        let review = "#[cfg_attr(test, derive(Debug))]\npub struct S;\n\
                      pub static N: u8 = 0;\npub fn f(_: &'static str) -> bool {\n    \
                      cfg!(test)\n}\n";
        assert_eq!(problems(review), Vec::<String>::new());
    }

    #[test]
    fn the_paths_of_the_extractability_sections_are_read() {
        let tracked = [
            (FILE, ""),
            ("kernel/x/src/b/c.rs", ""),
            ("kernel/x/Cargo.toml", ""),
        ];
        let (files, problems) = listed(&tree(&["kernel/x"], &tracked));
        assert_eq!(Vec::from_iter(files), [FILE, "kernel/x/src/b/c.rs"]);
        assert_eq!(problems, Vec::<String>::new());
        // A line that names no tracked `.rs` file.
        for line in [
            "kernel/x/src/absent.rs",
            "kernel/x/Cargo.toml",
            "",
            "kernel/x/src/",
            "kernel/x/../x/src/a.rs",
            " kernel/x/src/a.rs",
            "kernel/x/src/a",
        ] {
            let (files, problems) = listed(&tree(&[line, FILE], &tracked));
            assert_eq!(Vec::from_iter(files), [FILE], "{line:?}");
            let problem = format!("{CONTRACT}: {line:?} names no tracked .rs file");
            assert_eq!(problems, [problem]);
        }
        // A block right after the heading, a block that is not closed, an
        // empty block, and a contract without a block or outside the domains.
        let block = |text: &str| format!("# C\n\n## Extractability\n{text}");
        for (path, text, count) in [
            (CONTRACT, block(&format!("```paths\n{FILE}\n```\n")), 1),
            (CONTRACT, block(&format!("\n```paths\n{FILE}\n")), 1),
            (CONTRACT, block("\n```paths\n```\n"), 0),
            (CONTRACT, block("\nThe component has no code yet.\n"), 0),
            (
                "docs/domains/d/contract.md",
                block(&format!("```paths\n{FILE}\n```\n")),
                0,
            ),
        ] {
            let (files, problems) = listed(&Tree::from_files(&[(path, &text), (FILE, "")]));
            assert_eq!((files.len(), problems), (count, Vec::new()), "{text}");
        }
        // Other fences, white space at the end of a line or around the info
        // string, Windows line ends and an indented heading: each block is
        // read.
        for text in [
            format!("## Extractability\n\n``` paths\n{FILE}\n```\n"),
            format!("## Extractability\n\n````paths \n{FILE}\n````\n"),
            format!("## Extractability\n\n~~~paths\n{FILE}  \n~~~\n"),
            format!("## Extractability \r\n\r\n```paths\r\n{FILE}\r\n```\r\n"),
            format!(" ##  Extractability\n\n  ```paths\n{FILE}\n  ```\n## Next\n"),
        ] {
            let (files, problems) = listed(&Tree::from_files(&[(CONTRACT, &text), (FILE, "")]));
            assert_eq!(
                (Vec::from_iter(files), problems),
                (vec![FILE.into()], vec![]),
                "{text:?}"
            );
        }
        // Inside a block, a line of another fence, a heading of a block that
        // is not closed, and a fence of fewer than three characters are paths.
        for (text, line) in [
            (format!("```paths\n{FILE}\n```rust\n```\n"), "```rust"),
            (format!("```paths\n{FILE}\n## Next\n"), "## Next"),
            (format!("```paths\n{FILE}\n``\n```\n"), "``"),
        ] {
            let tree = Tree::from_files(&[(CONTRACT, &block(&text)), (FILE, "")]);
            let (files, problems) = listed(&tree);
            assert_eq!(Vec::from_iter(files), [FILE], "{text:?}");
            let problem = format!("{CONTRACT}: {line:?} names no tracked .rs file");
            assert!(problems.contains(&problem), "{problems:?}");
        }
    }

    #[test]
    fn a_listed_file_that_cannot_be_read_fails() {
        let mut tree = tree(&[FILE], &[(FILE, "pub fn f( {}\n")]);
        let roots = [(FILE.to_string(), true)];
        let (_, problems) = check(&tree, &roots);
        assert_eq!(problems.len(), 1);
        assert!(
            problems[0].starts_with(&format!("{FILE}: does not parse: ")),
            "{problems:?}"
        );
        for entry in [Entry::File(vec![0xff]), Entry::Symlink("b.rs".into())] {
            tree.insert(FILE, entry);
            let problem = format!("{FILE}: not a UTF-8 regular file");
            assert_eq!(check(&tree, &roots), (1, vec![problem]));
        }
    }

    /// The source of a crate whose handle type `ReplyRight` the guard of
    /// rule 6, when `guarded`, keeps from implementing `Clone`.
    fn handle(guarded: bool) -> String {
        let guard = "\n// Does not compile once `ReplyRight` implements `Clone`, and so `Copy`.\n\
                     const _: () = {\n    trait AmbiguousIfClone<A> {\n        const CHECK: () = ();\n    }\n    \
                     impl<T: ?Sized> AmbiguousIfClone<()> for T {}\n    \
                     impl<T: ?Sized + Clone> AmbiguousIfClone<u8> for T {}\n    \
                     <ReplyRight as AmbiguousIfClone<_>>::CHECK\n};\n";
        let source = "#![no_std]\n\npub struct ReplyRight {\n    slot: u32,\n}\n\n\
                      impl ReplyRight {\n    pub fn slot(&self) -> u32 {\n        self.slot\n    }\n}\n";
        format!("{source}{}", if guarded { guard } else { "" })
    }

    /// A workspace of its own below `fixture/`, with the crate of
    /// [`handle`].
    fn workspace(guarded: bool) -> Tree {
        let manifest = "[package]\nname = \"fixture\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n[workspace]\n";
        let lock = "# This file is automatically @generated by Cargo.\n\
                    # It is not intended for manual editing.\nversion = 4\n\n\
                    [[package]]\nname = \"fixture\"\nversion = \"0.0.0\"\n";
        let source = handle(guarded);
        let files = [
            ("fixture/Cargo.toml", manifest),
            ("fixture/Cargo.lock", lock),
        ];
        let mut tree = Tree::from_files(&files);
        tree.insert("fixture/src/lib.rs", Entry::File(source.into_bytes()));
        tree.insert("elsewhere/src/lib.rs", Entry::File(b"not Rust".to_vec()));
        tree
    }

    /// The case that derives `Clone` for `ReplyRight`.
    fn clone_case(error: &str) -> Case {
        let (find, file) = ("pub struct ReplyRight {", "fixture/src/lib.rs".to_string());
        let replace = format!("#[derive(Clone)]\n{find}");
        Case {
            file,
            find: find.into(),
            replace,
            error: error.into(),
        }
    }

    #[test]
    fn deriving_clone_for_a_guarded_handle_fails_the_build() {
        let scratch = crate::scratch::Scratch::new("compile-fail");
        let work = scratch.0.join("copy");
        let (guarded, case) = (workspace(true), clone_case("E0283"));
        assert_eq!(build(&guarded, "fixture", None, &work), Ok(()));
        assert_eq!(build(&guarded, "fixture", Some(&case), &work), Ok(()));
        assert!(!work.exists(), "the copy is removed");
        let unguarded = workspace(false);
        let built = build(&unguarded, "fixture", Some(&case), &work);
        assert_eq!(built, Err("the build succeeds".to_string()));
        let built = build(&guarded, "fixture", Some(&clone_case("E0599")), &work);
        let error = built.expect_err("another error");
        assert!(
            error.starts_with("the build fails without error[E0599]:\n"),
            "{error}"
        );
        assert!(error.contains("error[E0283]"), "{error}");
    }

    #[test]
    fn the_error_code_must_head_a_diagnostic_of_the_build() {
        let scratch = crate::scratch::Scratch::new("compile-fail-code");
        let work = scratch.0.join("copy");
        let tree = workspace(true);
        // A change that fails the build for another reason on a line that
        // holds the code, which the diagnostic quotes; text that is no error
        // code; part of the code; and no code.
        let typo = Case {
            replace: "#[derive(Clone) // error[E0283]\npub struct ReplyRight {".into(),
            ..clone_case("E0283")
        };
        let without = |code: &str| format!("the build fails without error[{code}]:\n");
        for (case, code) in [
            (typo, "E0283"),
            (clone_case("derive(Clone)"), "derive(Clone)"),
            (clone_case("E028"), "E028"),
            (clone_case(""), ""),
        ] {
            let error = build(&tree, "fixture", Some(&case), &work).expect_err(code);
            assert!(error.starts_with(&without(code)), "{error}");
            assert!(
                code != "E0283" || error.contains("// error[E0283]"),
                "{error}"
            );
        }
        assert!(!work.exists());
    }

    #[test]
    fn a_case_that_cannot_be_applied_fails() {
        let scratch = crate::scratch::Scratch::new("compile-fail-case");
        let work = scratch.0.join("copy");
        let tree = workspace(true);
        let file = "fixture/src/lib.rs";
        for (find, error) in [
            (
                "pub struct Absent {",
                format!("find occurs 0 times in {file}"),
            ),
            ("u32", format!("find occurs 2 times in {file}")),
        ] {
            let case = Case {
                find: find.into(),
                ..clone_case("E0283")
            };
            assert_eq!(build(&tree, "fixture", Some(&case), &work), Err(error));
        }
        let elsewhere = Case {
            file: "elsewhere/src/lib.rs".into(),
            ..clone_case("E0283")
        };
        let error = "elsewhere/src/lib.rs is no tracked UTF-8 file of fixture".to_string();
        assert_eq!(build(&tree, "fixture", Some(&elsewhere), &work), Err(error));
        let case = "file = \"a\"\nfind = \"b\"\nreplace = \"c\"\nerror = \"d\"\nextra = 1\n";
        assert!(toml::from_str::<Case>(case).is_err());
        assert!(toml::from_str::<Case>(&case.replace("extra = 1\n", "")).is_ok());
        assert!(!work.exists());
    }

    /// Runs the step on a Git repository of `files` and a lock of its
    /// kernel workspace, below the build directory, so that the pinned
    /// toolchain builds it.
    fn step(files: &[(&str, &str)]) -> (Facts, Result<(), String>) {
        let scratch = crate::scratch::Scratch::new("subset-step");
        files
            .iter()
            .for_each(|(path, text)| scratch.write(path, text));
        scratch.lock();
        for args in [&["init", "--quiet"][..], &["add", "--all"]] {
            let status = std::process::Command::new("git")
                .args(args)
                .current_dir(&scratch.0)
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .env("GIT_CONFIG_GLOBAL", "/dev/null")
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        }
        let mut facts = Facts::new();
        let result = run(&scratch.0, &mut facts);
        let work = format!("artifacts/subset/{}", std::process::id());
        assert!(!scratch.0.join(work).exists(), "the copies are removed");
        (facts, result)
    }

    #[test]
    fn the_step_checks_the_listed_files_and_runs_the_cases() {
        let case = "file = \"kernel/x/src/lib.rs\"\nfind = \"pub struct ReplyRight {\"\n\
                    replace = \"#[derive(Clone)]\\npub struct ReplyRight {\"\nerror = \"E0283\"\n";
        let guarded = format!("{}\n#[cfg(test)]\nmod tests;\n", handle(true));
        let unguarded = format!("{}\n#[cfg(test)]\nmod tests;\n", handle(false));
        let broken = format!("{guarded}\npub fn broken() -> u8 {{\n    \"\"\n}}\n");
        let repository = |lib: &str| {
            step(&[
                (
                    "kernel/Cargo.toml",
                    "[workspace]\nresolver = \"3\"\nmembers = [\"x\"]\n",
                ),
                (
                    "kernel/x/Cargo.toml",
                    "[package]\nname = \"x\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
                ),
                ("kernel/x/src/lib.rs", lib),
                ("kernel/x/src/tests.rs", "static mut T: u8 = 0;\n"),
                ("kernel/x/compile-fail/clone.toml", case),
                ("kernel/x/cases/clone.toml", "not a case"),
                (CONTRACT, &contract(&["kernel/x/src"])),
            ])
        };
        // The roots from `cargo metadata` make the test module file test
        // code, and the case holds with the guard.
        let (facts, result) = repository(&guarded);
        assert_eq!(result, Ok(()));
        let counts = [("files", "1"), ("compile-fail cases", "1")];
        assert_eq!(
            facts,
            counts.map(|(name, count)| (name.into(), count.into()))
        );
        // Without the guard, the case fails, and a broken workspace fails
        // before its cases.
        let failed = repository(&unguarded).1.expect_err("the build succeeds");
        assert!(
            failed.starts_with("kernel/x/compile-fail/clone.toml: the build succeeds"),
            "{failed}"
        );
        let failed = repository(&broken).1.expect_err("the build fails");
        assert!(failed.starts_with("kernel: the build fails:\n"), "{failed}");
        assert!(failed.contains("error[E0308]"), "{failed}");
    }
}
