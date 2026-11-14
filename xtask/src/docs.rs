//! The documentation step: relative links and anchors in Markdown and the
//! `cargo xtask` commands that documents mention.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use crate::COMMANDS;
use crate::repo::{self, Tree};

/// The marker that exempts a mention of a command that does not exist yet.
pub const PLANNED: &str = "(planned)";

/// The documentation step.
pub fn run(root: &Path) -> Result<(), String> {
    let problems = check(&Tree::load(root)?);
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// Every documentation problem in `tree`.
pub fn check(tree: &Tree) -> Vec<String> {
    let mut problems = Vec::new();
    for (path, text) in tree.texts().filter(|(path, _)| path.ends_with(".md")) {
        check_links(tree, path, text, &mut problems);
        check_mentions(path, text, &mut problems);
    }
    problems
}

/// The line number of the byte at `offset`.
fn line_of(source: &str, offset: usize) -> usize {
    source[..offset].matches('\n').count() + 1
}

/// One line of a Markdown file and whether it belongs to a fenced code
/// block (fence lines included).
struct Line<'a> {
    start: usize,
    text: &'a str,
    code: bool,
}

fn lines(source: &str) -> Vec<Line<'_>> {
    let mut lines = Vec::new();
    let mut fence: Option<(char, usize)> = None;
    let mut start = 0;
    for raw in source.split_inclusive('\n') {
        let text = raw.trim_end_matches(['\n', '\r']);
        let indent = text.len() - text.trim_start_matches(' ').len();
        let body = &text[indent..];
        let marker = body.chars().next().filter(|c| *c == '`' || *c == '~');
        let run = marker.map_or(0, |m| body.chars().take_while(|c| *c == m).count());
        let code = match fence {
            Some((open, length)) => {
                if indent <= 3
                    && marker == Some(open)
                    && run >= length
                    && body[run..].trim().is_empty()
                {
                    fence = None;
                }
                true
            }
            None => {
                let opens =
                    indent <= 3 && run >= 3 && !(marker == Some('`') && body[run..].contains('`'));
                if opens {
                    fence = marker.map(|m| (m, run));
                }
                opens
            }
        };
        lines.push(Line { start, text, code });
        start += raw.len();
    }
    lines
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// Prose outside code.
    Text,
    /// The content of an inline code span.
    Code,
    /// One line of a fenced code block.
    Block,
}

/// A piece of a Markdown file. `end` is the offset just after the piece,
/// including the closing backticks of a code span.
struct Segment<'a> {
    kind: Kind,
    text: &'a str,
    start: usize,
    end: usize,
}

fn segments(source: &str) -> Vec<Segment<'_>> {
    let mut segments = Vec::new();
    let mut prose_start: Option<usize> = None;
    for line in lines(source) {
        if line.code {
            if let Some(from) = prose_start.take() {
                split_prose(source, from, line.start, &mut segments);
            }
            segments.push(Segment {
                kind: Kind::Block,
                text: line.text,
                start: line.start,
                end: line.start + line.text.len(),
            });
        } else if prose_start.is_none() {
            prose_start = Some(line.start);
        }
    }
    if let Some(from) = prose_start {
        split_prose(source, from, source.len(), &mut segments);
    }
    segments
}

/// Splits prose into text and inline code spans. A run of backticks opens a
/// span that the next run of the same length closes; an unmatched run is
/// literal text.
fn split_prose<'a>(source: &'a str, from: usize, to: usize, out: &mut Vec<Segment<'a>>) {
    let bytes = source.as_bytes();
    let run_at = |at: usize| {
        bytes[at..to]
            .iter()
            .take_while(|byte| **byte == b'`')
            .count()
    };
    let mut text_start = from;
    let mut at = from;
    while at < to {
        if bytes[at] != b'`' {
            at += 1;
            continue;
        }
        let open = run_at(at);
        let mut close = None;
        let mut scan = at + open;
        while scan < to {
            if bytes[scan] == b'`' {
                let run = run_at(scan);
                if run == open {
                    close = Some(scan);
                    break;
                }
                scan += run;
            } else {
                scan += 1;
            }
        }
        let Some(close) = close else {
            at += open;
            continue;
        };
        out.push(Segment {
            kind: Kind::Text,
            text: &source[text_start..at],
            start: text_start,
            end: at,
        });
        out.push(Segment {
            kind: Kind::Code,
            text: &source[at + open..close],
            start: at,
            end: close + open,
        });
        at = close + open;
        text_start = at;
    }
    out.push(Segment {
        kind: Kind::Text,
        text: &source[text_start..to],
        start: text_start,
        end: to,
    });
}

/// The link targets in a piece of prose, with their offsets: inline links
/// and images, reference definitions, and `href`, `src` and `srcset`
/// attributes of HTML. `at_line_start` tells whether the piece starts a line;
/// a reference definition must.
fn link_targets(text: &str, at_line_start: bool) -> Vec<(usize, &str)> {
    let mut targets = Vec::new();
    for (at, _) in text.match_indices("](") {
        let rest = &text[at + 2..];
        let target = if let Some(inner) = rest.strip_prefix('<') {
            inner.find('>').map(|end| &inner[..end])
        } else {
            let mut depth = 0usize;
            let mut end = None;
            for (index, c) in rest.char_indices() {
                match c {
                    '(' => depth += 1,
                    ')' if depth == 0 => {
                        end = Some(index);
                        break;
                    }
                    ')' => depth -= 1,
                    c if c.is_whitespace() => {
                        end = Some(index);
                        break;
                    }
                    _ => {}
                }
            }
            end.map(|end| &rest[..end])
        };
        if let Some(target) = target {
            targets.push((at + 2, target));
        }
    }
    let mut offset = 0;
    for (index, line) in text.split_inclusive('\n').enumerate() {
        let trimmed = line.trim_start();
        if (index > 0 || at_line_start)
            && trimmed.starts_with('[')
            && line.len() - trimmed.len() <= 3
            && let Some(close) = trimmed.find("]:")
            && let Some(target) = trimmed[close + 2..].split_whitespace().next()
        {
            targets.push((offset, target.trim_start_matches('<').trim_end_matches('>')));
        }
        offset += line.len();
    }
    for attribute in ["href=\"", "src=\"", "srcset=\""] {
        for (at, _) in text.match_indices(attribute) {
            let rest = &text[at + attribute.len()..];
            let Some(end) = rest.find('"') else { continue };
            for candidate in rest[..end].split(',') {
                if let Some(target) = candidate.split_whitespace().next() {
                    targets.push((at, target));
                }
            }
        }
    }
    targets
}

fn check_links(tree: &Tree, path: &str, source: &str, problems: &mut Vec<String>) {
    for segment in segments(source) {
        if segment.kind != Kind::Text {
            continue;
        }
        let at_line_start = segment.start == 0 || source[..segment.start].ends_with('\n');
        for (offset, target) in link_targets(segment.text, at_line_start) {
            let line = line_of(source, segment.start + offset);
            if let Some(problem) = check_target(tree, path, target) {
                problems.push(format!("{path}:{line}: link `{target}`: {problem}"));
            }
        }
    }
}

/// Why a link target from `from` is broken, if it is.
fn check_target(tree: &Tree, from: &str, target: &str) -> Option<String> {
    let external =
        target.contains("://") || target.starts_with("mailto:") || target.starts_with("tel:");
    if target.is_empty() || external {
        return None;
    }
    let (file, anchor) = match target.split_once('#') {
        Some((file, anchor)) => (file, Some(anchor)),
        None => (target, None),
    };
    let resolved = if file.is_empty() {
        Some(from.to_string())
    } else if let Some(absolute) = file.strip_prefix('/') {
        repo::join("", absolute)
    } else {
        repo::join(repo::parent(from), file)
    };
    let Some(resolved) = resolved else {
        return Some("leaves the repository".to_string());
    };
    if !tree.exists(&resolved) {
        return Some(format!("{resolved} is not a tracked file or directory"));
    }
    match (anchor, tree.text(&resolved)) {
        (Some(anchor), Some(markdown))
            if resolved.ends_with(".md") && !anchors(markdown).contains(anchor) =>
        {
            Some(format!(
                "{resolved} has no heading with the anchor #{anchor}"
            ))
        }
        _ => None,
    }
}

/// The anchors GitHub generates for the ATX headings of a Markdown file.
pub fn anchors(markdown: &str) -> BTreeSet<String> {
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut anchors = BTreeSet::new();
    for line in lines(markdown) {
        if line.code {
            continue;
        }
        let Some(title) = heading(line.text) else {
            continue;
        };
        let base = slug(&plain(title));
        let count = seen.entry(base.clone()).or_insert(0);
        anchors.insert(if *count == 0 {
            base.clone()
        } else {
            format!("{base}-{count}")
        });
        *count += 1;
    }
    anchors
}

/// The text of an ATX heading line.
fn heading(line: &str) -> Option<&str> {
    let indent = line.len() - line.trim_start_matches(' ').len();
    if indent > 3 {
        return None;
    }
    let body = &line[indent..];
    let level = body.chars().take_while(|c| *c == '#').count();
    if !(1..=6).contains(&level) {
        return None;
    }
    let rest = &body[level..];
    if !rest.is_empty() && !rest.starts_with([' ', '\t']) {
        return None;
    }
    let rest = rest.trim();
    let without_closing = rest.trim_end_matches('#');
    let title = if without_closing.is_empty() || without_closing.ends_with([' ', '\t']) {
        without_closing.trim_end()
    } else {
        rest
    };
    Some(title)
}

/// Heading text as rendered: code, emphasis and link markup removed.
fn plain(title: &str) -> String {
    let chars: Vec<char> = title.chars().collect();
    let mut out = String::new();
    let mut at = 0;
    while at < chars.len() {
        match chars[at] {
            '`' | '*' | '[' => {}
            ']' if chars.get(at + 1) == Some(&'(') => {
                let mut depth = 0usize;
                at += 1;
                while at < chars.len() {
                    match chars[at] {
                        '(' => depth += 1,
                        ')' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                    at += 1;
                }
            }
            ']' => {}
            c => out.push(c),
        }
        at += 1;
    }
    out
}

/// GitHub's anchor for a heading: lower case, punctuation removed, spaces
/// replaced by hyphens.
fn slug(title: &str) -> String {
    title
        .trim()
        .to_lowercase()
        .chars()
        .filter_map(|c| match c {
            ' ' => Some('-'),
            c if c.is_alphanumeric() || c == '-' || c == '_' => Some(c),
            _ => None,
        })
        .collect()
}

/// A `cargo xtask` mention: the offset of `cargo` and the command words
/// that follow `xtask`.
fn find_mentions(text: &str) -> Vec<(usize, Vec<&str>)> {
    let tokens: Vec<(usize, &str)> = text
        .split_whitespace()
        .map(|token| (token.as_ptr() as usize - text.as_ptr() as usize, token))
        .collect();
    let is_word = |token: &str| {
        let mut chars = token.chars();
        chars.next().is_some_and(|c| c.is_ascii_lowercase())
            && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
    };
    let mut mentions = Vec::new();
    for (index, window) in tokens.windows(2).enumerate() {
        if window[0].1 == "cargo" && window[1].1 == "xtask" {
            let words = tokens[index + 2..]
                .iter()
                .map(|(_, token)| *token)
                .take_while(|token| is_word(token))
                .collect();
            mentions.push((window[0].0, words));
        }
    }
    mentions
}

/// Whether `words` name a command of `cargo xtask`. Words after a command
/// without subcommands are its arguments.
pub fn resolves(words: &[&str]) -> bool {
    let mut level = COMMANDS;
    for word in words {
        if level.is_empty() {
            return true;
        }
        match level.iter().find(|command| command.name == *word) {
            Some(command) => level = command.subcommands,
            None => return false,
        }
    }
    true
}

fn check_mentions(path: &str, source: &str, problems: &mut Vec<String>) {
    for segment in segments(source) {
        for (offset, words) in find_mentions(segment.text) {
            let line = line_of(source, segment.start + offset);
            let command = format!("cargo xtask {}", words.join(" "));
            let command = command.trim_end();
            let planned = segment.kind == Kind::Code
                && source[segment.end..].trim_start().starts_with(PLANNED);
            let problem = match (segment.kind, planned, resolves(&words)) {
                (Kind::Text, _, _) => Some("write `cargo xtask` commands as code".to_string()),
                (_, true, true) => Some(format!("`{command}` exists; remove the {PLANNED} marker")),
                (_, false, false) => Some(format!(
                    "`{command}` is not a command; mark a planned command with {PLANNED} after the code span"
                )),
                _ => None,
            };
            if let Some(problem) = problem {
                problems.push(format!("{path}:{line}: {problem}"));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn problems(files: &[(&str, &str)]) -> Vec<String> {
        check(&Tree::from_files(files))
    }

    #[test]
    fn valid_links_and_anchors_pass() {
        let readme = "# Title\n\nSee [the guide](docs/guide.md#first-steps), [again](docs/guide.md#notes-1),\n\
            [here](#title), [the folder](docs/), [a site](https://example.org/x#y) and\n\
            <img src=\"docs/logo.svg\" alt=\"\">.\n\n[ref]: docs/guide.md\n";
        let guide =
            "# Guide\n\n## First steps\n\n## Notes\n\n## Notes\n\n```sh\n# not a heading\n```\n";
        assert_eq!(
            problems(&[
                ("README.md", readme),
                ("docs/guide.md", guide),
                ("docs/logo.svg", "<svg/>")
            ]),
            Vec::<String>::new()
        );
    }

    #[test]
    fn rejects_a_dead_link() {
        let found = problems(&[("README.md", "See [the guide](docs/missing.md).\n")]);
        assert_eq!(found.len(), 1, "{found:?}");
        assert!(
            found[0].starts_with("README.md:1: link `docs/missing.md`"),
            "{found:?}"
        );
    }

    #[test]
    fn rejects_a_missing_anchor_and_a_link_out_of_the_repository() {
        let found = problems(&[
            ("README.md", "[a](docs/a.md#absent)\n[b](../outside.md)\n"),
            ("docs/a.md", "# Present\n"),
        ]);
        assert_eq!(found.len(), 2, "{found:?}");
        assert!(
            found[0].contains("no heading with the anchor #absent"),
            "{found:?}"
        );
        assert!(found[1].contains("leaves the repository"), "{found:?}");
    }

    #[test]
    fn reference_definitions_start_a_line() {
        let readme = "Write `x` [label]: not-a-link and\n[label]: README.md\n";
        assert_eq!(problems(&[("README.md", readme)]), Vec::<String>::new());
        let found = problems(&[("README.md", "[label]: missing.md\n")]);
        assert_eq!(found.len(), 1, "{found:?}");
    }

    #[test]
    fn links_inside_code_are_not_checked() {
        let readme = "Write `[x](missing.md)` like this:\n\n```md\n[y](missing.md)\n```\n";
        assert_eq!(problems(&[("README.md", readme)]), Vec::<String>::new());
    }

    #[test]
    fn computes_github_anchors() {
        let markdown = "# Release notes\n## `cargo xtask check`\n## What's new?\n\
            ## Notes\n## Notes\n## Link to [the guide](guide.md) ##\n    # indented code\n#hashtag\n";
        let expected = [
            "cargo-xtask-check",
            "link-to-the-guide",
            "notes",
            "notes-1",
            "release-notes",
            "whats-new",
        ];
        assert_eq!(
            anchors(markdown),
            expected.iter().map(|s| s.to_string()).collect()
        );
    }

    #[test]
    fn accepts_existing_and_planned_commands() {
        let readme = "Run `cargo xtask check` or `cargo xtask`.\n\n`cargo xtask docs index` (planned)\n\
            and `cargo xtask formal frobnicate --base REV`\n(planned) later.\n\n```sh\ncargo xtask check\n```\n";
        assert_eq!(problems(&[("README.md", readme)]), Vec::<String>::new());
    }

    #[test]
    fn rejects_a_command_that_does_not_exist() {
        let found = problems(&[("docs/a.md", "Run `cargo xtask frobnicate --all`.\n")]);
        assert_eq!(found.len(), 1, "{found:?}");
        assert!(
            found[0].contains("`cargo xtask frobnicate` is not a command"),
            "{found:?}"
        );
    }

    #[test]
    fn rejects_a_missing_command_in_a_code_block() {
        let found = problems(&[("docs/a.md", "```sh\ncargo xtask frobnicate\n```\n")]);
        assert_eq!(found.len(), 1, "{found:?}");
    }

    #[test]
    fn rejects_a_stale_planned_marker() {
        let found = problems(&[(
            "docs/a.md",
            "Text.\n\n`cargo xtask check` (planned) runs.\n",
        )]);
        assert_eq!(found.len(), 1, "{found:?}");
        assert!(found[0].starts_with("docs/a.md:3:"), "{found:?}");
        assert!(
            found[0].contains("remove the (planned) marker"),
            "{found:?}"
        );
    }

    #[test]
    fn rejects_a_command_written_as_prose() {
        let found = problems(&[("docs/a.md", "Run cargo xtask check first.\n")]);
        assert_eq!(found.len(), 1, "{found:?}");
        assert!(found[0].contains("as code"), "{found:?}");
    }
}
