//! Check that the annotated spike documents and their authored Lean views agree.
//!
//! This is the port of `check-spike-sources.ps1`, which was PowerShell-only and
//! therefore unrunnable on a Linux developer host.
//!
//! `docs/SPIKE_AUTHORING.md` is the contract. Each `docs/SPIKE_<n>.md` is prose
//! around fenced code blocks, and every one of those blocks carries a
//! classification comment on the line immediately above it saying what the block
//! is:
//!
//! - `authored file=<path>` -- this block is the verbatim content of
//!   `Spikes/<directory>/<path>`. The document and the file are two views of one
//!   source, and this tool is what makes that true rather than aspirational.
//! - `generated id=<id> derives=<authority>` -- output of some generator, with the
//!   authority that produced it named.
//! - `interface id=<id>` / `proof-sketch id=<id>` -- illustrative, not a file.
//!
//! Three things are checked, and they are why the classification exists at all.
//! Every block must be classified, so that no code in a spike document is of
//! unstated provenance. Every block's identity must be unique, so that two blocks
//! cannot both claim to be the same file or the same generated artefact. And the
//! `authored` blocks must form a manifest that agrees exactly -- set and content --
//! with the `.lean` files in the spike's directory, so a reviewer reading the
//! annotated document has read the compiled source.
//!
//! `README.md` is explicit that this is "a corpus consistency check, not
//! compilation or proof checking". The `Spikes/` files are authoring fixtures and
//! are not expected to compile; what they are expected to do is match the document
//! that explains them.
//!
//! # An audit of nothing is not a clean audit
//!
//! `check-spike-sources.ps1` reported success whenever its failure flag was clear,
//! and the flag stays clear over an empty corpus. Two routes reached that. Passing
//! `-Spike @()` selected no documents, so the `foreach` body never ran and the
//! script printed "All selected spike blocks are classified, uniquely identified,
//! and exact authored sources match their directories." over nothing. And a
//! document with no fenced blocks paired with a directory with no `.lean` files
//! compared an empty manifest against an empty manifest, agreed, and passed.
//!
//! [`check_spike`] refuses both, and refuses them narrowly. A selection that names
//! no spike is refused before any work. A spike whose document declares no
//! `authored` block *and* whose directory holds no `.lean` file is reported as an
//! unchecked spike -- but only when both sides are empty, because either side
//! being empty on its own already produces the original's manifest-difference
//! finding, which is the better message and is left alone. See
//! `an_empty_selection_is_refused`, `a_spike_with_no_blocks_and_no_files_is_refused`
//! and `one_empty_side_is_an_ordinary_manifest_finding_not_a_refusal`.
//!
//! # Deliberate departures from the PowerShell, each of them a defect report
//!
//! These are stated rather than quietly applied, because a port that changes a
//! gate's verdict without saying so is the thing this repository keeps being
//! burned by.
//!
//! - **Content and manifest comparison is ordinal.** The original used `-cne` and
//!   `Sort-Object -CaseSensitive`. PowerShell's case-sensitive operators are still
//!   *culture-sensitive*, which can equate distinct Unicode spellings -- exactly
//!   the defect `audit-trust.ps1` documents in its own `Get-RejectedAxiom` and
//!   works around with `StringComparison::Ordinal`. The same author did not carry
//!   that fix here, so two authored sources differing only by a culture-ignorable
//!   character compared equal. Ordinal comparison can only produce more findings
//!   than the original, never fewer.
//!
//! - **Only files enter the manifest.** The original's
//!   `Get-ChildItem -Filter '*.lean' -Recurse` omitted `-File` (which
//!   `audit-trust.ps1`'s equivalent walk does pass), so a *directory* named
//!   `something.lean` would have entered the directory manifest as an authored file
//!   that no block can ever match. There is no such directory in `Spikes/` today.
//!
//! - **The manifest difference is printed as a list, not a `Format-Table`.** The
//!   finding line above it -- `SPIKE_n: authored file manifest differs` -- is
//!   unchanged; only the diagnostic underneath it is rendered differently, because
//!   `Compare-Object | Format-Table` has no meaningful Rust spelling and the table
//!   was harder to read than the two lists it summarised.
//!
//! - **Findings go to standard error.** The original used `Write-Host`, which is
//!   the host stream. Both are captured by CI; a developer piping the tool now gets
//!   the findings separated from the passing line.
//!
//! One defect is reproduced rather than fixed, because fixing it would change which
//! findings the gate produces: see [`is_lean_fence`].
//!
//! Exit status is 1 on any finding and on any unchecked spike.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use regex::Regex;

/// The five spikes, and the directory each document's authored blocks mirror.
///
/// `docs/SPIKE_<number>.md` against `Spikes/<directory>`. Closed by construction:
/// `docs/SPIKE_IMPLEMENTATION_PLAN.md` fixes the corpus at five.
const SPIKES: &[(u32, &str)] = &[
    (1, "1_Hello_World"),
    (2, "2_Sort"),
    (3, "3_Gzip"),
    (4, "4_Web_Server"),
    (5, "5_Spinning_Cube"),
];

/// The classification comment that must sit on the line immediately above a fence.
///
/// Case-insensitive because PowerShell's `-match` is, so a document the original
/// accepted is not newly rejected here.
const CLASSIFICATION_PATTERN: &str = r"(?i)^<!-- grass-block: (.+) -->$";

/// `authored file=<path>` -- the block is the verbatim content of a file.
const AUTHORED_PATTERN: &str = r"(?i)^authored file=([^ ]+)$";

/// `generated id=<id> derives=<authority>` -- generator output, with its authority.
const GENERATED_PATTERN: &str = r"(?i)^generated id=([^ ]+) derives=(.+)$";

/// `interface id=<id>` / `proof-sketch id=<id>` -- illustrative blocks.
const ILLUSTRATIVE_PATTERN: &str = r"(?i)^(interface|proof-sketch) id=([^ ]+)$";

/// Whether a fence opens a Lean block.
///
/// An `authored` block must be `` ```lean ``, since it claims to be the content of
/// a `.lean` file. The comparison is case-insensitive, which is a defect: it is the
/// original's `-ne`, and the rest of this tool is deliberately ordinal. It is
/// reproduced rather than corrected because tightening it could newly fail a
/// document the gate has been passing, which is a change of verdict and belongs in
/// its own change. No document in the corpus writes the fence any way but
/// lowercase.
fn is_lean_fence(line: &str) -> bool {
    line.eq_ignore_ascii_case("```lean")
}

/// Line endings normalised and trailing blank lines removed.
///
/// Both sides of every content comparison go through this, so a document checked
/// out with CRLF and a file checked out with LF are still one source. Trailing
/// newlines are stripped entirely, not just reduced to one, because a fenced block
/// cannot represent the presence or absence of a final newline and it would be a
/// difference nobody could act on.
fn normalize_source(text: &str) -> String {
    let unified = text.replace("\r\n", "\n").replace('\r', "\n");
    unified.trim_end_matches('\n').to_string()
}

/// The compiled patterns, built once.
struct Patterns {
    classification: Regex,
    authored: Regex,
    generated: Regex,
    illustrative: Regex,
}

impl Patterns {
    fn new() -> Self {
        Self {
            classification: Regex::new(CLASSIFICATION_PATTERN).expect("constant"),
            authored: Regex::new(AUTHORED_PATTERN).expect("constant"),
            generated: Regex::new(GENERATED_PATTERN).expect("constant"),
            illustrative: Regex::new(ILLUSTRATIVE_PATTERN).expect("constant"),
        }
    }
}

/// What one spike document said.
#[derive(Debug, Default, PartialEq, Eq)]
struct Document {
    /// Every fenced block seen, classified or not. Zero means nothing was checked.
    blocks: usize,
    /// `authored` path to normalised block content, in path order.
    authored: BTreeMap<String, String>,
    /// One line per finding, in document order.
    findings: Vec<String>,
}

/// Read one spike document's blocks and their classifications.
///
/// The scan is the original's, step for step. A fence is any line starting with
/// three backticks; its classification is the line immediately above it and nowhere
/// else, which is what "immediate" in the finding text means; and the block runs to
/// the next line that is exactly three backticks. An unterminated block abandons the
/// rest of the document, because after it there is no way to tell prose from code.
fn read_document(patterns: &Patterns, number: u32, text: &str) -> Document {
    let normalized = normalize_source(text);
    let lines: Vec<&str> = normalized.split('\n').collect();

    let mut document = Document::default();
    let mut identities: BTreeSet<String> = BTreeSet::new();
    let mut index = 0;
    while index < lines.len() {
        if !lines[index].starts_with("```") {
            index += 1;
            continue;
        }

        document.blocks += 1;
        let block = document.blocks;
        let classification: Option<String> = if index == 0 {
            None
        } else {
            patterns
                .classification
                .captures(lines[index - 1])
                .map(|c| c[1].to_string())
        };
        if classification.is_none() {
            document.findings.push(format!(
                "SPIKE_{number}: block {block} has no immediate classification"
            ));
        }

        let mut closing = index + 1;
        while closing < lines.len() && lines[closing] != "```" {
            closing += 1;
        }
        if closing >= lines.len() {
            document
                .findings
                .push(format!("SPIKE_{number}: block {block} is unterminated"));
            break;
        }

        let content = if closing == index + 1 {
            String::new()
        } else {
            lines[index + 1..closing].join("\n")
        };

        if let Some(classification) = classification {
            let mut identity: Option<String> = None;
            if let Some(captured) = patterns.authored.captures(&classification) {
                let path = captured[1].replace('\\', "/");
                identity = Some(format!("authored:{path}"));
                if !is_lean_fence(lines[index]) {
                    document.findings.push(format!(
                        "SPIKE_{number}: authored {path} is not a Lean block"
                    ));
                }
                match document.authored.entry(path.clone()) {
                    // The *first* block to claim a path keeps it, as the original's
                    // `Dictionary.Add` guard did; a later one is a finding and its
                    // content is not compared against anything.
                    std::collections::btree_map::Entry::Vacant(slot) => {
                        slot.insert(normalize_source(&content));
                    }
                    std::collections::btree_map::Entry::Occupied(_) => document
                        .findings
                        .push(format!("SPIKE_{number}: duplicate authored path {path}")),
                }
            } else if let Some(captured) = patterns.generated.captures(&classification) {
                identity = Some(format!("generated:{}", &captured[1]));
                if captured[2].trim().is_empty() {
                    document.findings.push(format!(
                        "SPIKE_{number}: generated block lacks derives authority"
                    ));
                }
            } else if let Some(captured) = patterns.illustrative.captures(&classification) {
                identity = Some(format!("{}:{}", &captured[1], &captured[2]));
            } else {
                document.findings.push(format!(
                    "SPIKE_{number}: invalid classification '{classification}'"
                ));
            }

            if let Some(identity) = identity {
                if !identities.insert(identity.clone()) {
                    document.findings.push(format!(
                        "SPIKE_{number}: duplicate block identity {identity}"
                    ));
                }
            }
        }

        index = closing + 1;
    }
    document
}

/// Every `*.lean` file under `directory`, as a `/`-separated path relative to it.
///
/// Sorted ordinally. Files only; see the module comment.
fn lean_files(directory: &Path) -> Result<Vec<String>, String> {
    let mut found = Vec::new();
    walk(directory, "", &mut found)?;
    found.sort();
    Ok(found)
}

fn walk(directory: &Path, prefix: &str, found: &mut Vec<String>) -> Result<(), String> {
    let entries = fs::read_dir(directory)
        .map_err(|err| format!("check-spike-sources: {}: {err}", directory.display()))?;
    for entry in entries {
        let entry =
            entry.map_err(|err| format!("check-spike-sources: {}: {err}", directory.display()))?;
        let name = entry.file_name().to_string_lossy().into_owned();
        let relative = if prefix.is_empty() {
            name.clone()
        } else {
            format!("{prefix}/{name}")
        };
        let file_type = entry
            .file_type()
            .map_err(|err| format!("check-spike-sources: {}: {err}", entry.path().display()))?;
        if file_type.is_dir() {
            walk(&entry.path(), &relative, found)?;
        } else if name.ends_with(".lean") {
            found.push(relative);
        }
    }
    Ok(())
}

/// Compare one document's authored manifest against its directory.
///
/// Returns the findings, in the original's order: the manifest line (with the two
/// lists underneath it) first, then one line per file whose content differs.
fn compare_manifest(
    number: u32,
    directory_label: &str,
    document_label: &str,
    directory_files: &[String],
    authored: &BTreeMap<String, String>,
    read_file: &mut dyn FnMut(&str) -> Result<String, String>,
) -> Result<Vec<String>, String> {
    let mut findings = Vec::new();
    let document_paths: Vec<&String> = authored.keys().collect();
    let directory_matches_document = directory_files.len() == document_paths.len()
        && directory_files
            .iter()
            .zip(&document_paths)
            .all(|(a, b)| a == *b);
    if !directory_matches_document {
        findings.push(format!("SPIKE_{number}: authored file manifest differs"));
        let in_document: BTreeSet<&str> = authored.keys().map(String::as_str).collect();
        for path in directory_files {
            if !in_document.contains(path.as_str()) {
                findings.push(format!("  only in {directory_label}: {path}"));
            }
        }
        let on_disk: BTreeSet<&str> = directory_files.iter().map(String::as_str).collect();
        for path in document_paths {
            if !on_disk.contains(path.as_str()) {
                findings.push(format!("  only in {document_label}: {path}"));
            }
        }
    }

    for path in directory_files {
        let Some(expected) = authored.get(path) else {
            continue;
        };
        let actual = normalize_source(&read_file(path)?);
        if &actual != expected {
            findings.push(format!(
                "SPIKE_{number}: {path} differs from its authored block"
            ));
        }
    }
    Ok(findings)
}

/// Check one spike end to end.
fn check_spike(
    patterns: &Patterns,
    root: &Path,
    number: u32,
    directory_name: &str,
) -> Result<Vec<String>, String> {
    let document_label = format!("docs/SPIKE_{number}.md");
    let directory_label = format!("Spikes/{directory_name}");
    let document_path = root.join("docs").join(format!("SPIKE_{number}.md"));
    let directory_path = root.join("Spikes").join(directory_name);

    // Named before either is opened. The original used `$PSScriptRoot`, so it could
    // not be run against the wrong tree; this one can, and "The system cannot find
    // the path specified" is not a message that tells anybody what to do about it.
    for (label, path) in [
        (&document_label, &document_path),
        (&directory_label, &directory_path),
    ] {
        if !path.exists() {
            return Err(format!(
                "check-spike-sources: {label} does not exist, so spike {number} could not be \
                 checked.\nRun this from the repository root, or pass --root <path>."
            ));
        }
    }

    let text = read_utf8(&document_path)?;
    let document = read_document(patterns, number, &text);
    let directory_files = lean_files(&directory_path)?;

    // The empty-scan refusal, before any comparison. Stated as narrowly as it can
    // be: the manifest comparison compared nothing, on both sides at once. Every
    // other emptiness already fails through an ordinary finding -- a document with
    // no `authored` block against a populated directory is a manifest difference,
    // and so is the reverse -- and the original's message for those is the better
    // one, so it is left in place. Only the case where both sides are empty
    // produces agreement out of nothing, and that is what the original reported as
    // "All selected spike blocks are classified, uniquely identified, and exact
    // authored sources match their directories."
    if directory_files.is_empty() && document.authored.is_empty() {
        return Ok(vec![format!(
            "SPIKE_{number}: nothing was compared -- {document_label} declares no authored block \
             (it has {} fenced code block(s) in all) and {directory_label} contains no Lean \
             file.\nRefusing to report a spike as consistent when both sides of the comparison \
             were empty.",
            document.blocks
        )]);
    }

    let mut findings = document.findings.clone();
    findings.extend(compare_manifest(
        number,
        &directory_label,
        &document_label,
        &directory_files,
        &document.authored,
        &mut |path| {
            read_utf8(&directory_path.join(path.replace('/', std::path::MAIN_SEPARATOR_STR)))
        },
    )?);
    Ok(findings)
}

/// `Get-Content -Raw -Encoding utf8`, byte-order mark and all.
fn read_utf8(path: &Path) -> Result<String, String> {
    let text = fs::read_to_string(path)
        .map_err(|err| format!("check-spike-sources: {}: {err}", path.display()))?;
    Ok(text.strip_prefix('\u{feff}').unwrap_or(&text).to_string())
}

/// The spikes named by the command line, or all five.
///
/// The original's `[ValidateRange(1, 5)]`, plus the refusal the original lacked: a
/// selection that names nothing selects nothing and must not be reported as a clean
/// corpus.
fn selected_spikes(arguments: &[String]) -> Result<Vec<(u32, &'static str)>, String> {
    if arguments.is_empty() {
        return Ok(SPIKES.to_vec());
    }
    let mut chosen = Vec::new();
    for argument in arguments {
        let number: u32 = argument.parse().map_err(|_| {
            format!(
                "check-spike-sources: '{argument}' is not a spike number. Usage: spike-sources \
                 [--root <path>] [1..5 ...]"
            )
        })?;
        match SPIKES.iter().find(|(n, _)| *n == number) {
            Some(pair) => chosen.push(*pair),
            None => {
                return Err(format!(
                    "check-spike-sources: there is no spike {number}; the corpus is spikes 1 to 5."
                ))
            }
        }
    }
    if chosen.is_empty() {
        return Err(
            "check-spike-sources: no spike was selected, so nothing would be checked.\nRefusing \
             to report a clean corpus over an empty selection."
                .to_string(),
        );
    }
    Ok(chosen)
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let (root, rest) = match arguments.split_first() {
        Some((flag, rest)) if flag == "--root" => match rest.split_first() {
            Some((path, rest)) => (PathBuf::from(path), rest.to_vec()),
            None => {
                eprintln!("check-spike-sources: --root needs a path.");
                return ExitCode::FAILURE;
            }
        },
        _ => (PathBuf::from("."), arguments.clone()),
    };

    let patterns = Patterns::new();
    let result = selected_spikes(&rest).and_then(|spikes| {
        let mut findings = Vec::new();
        for (number, directory) in spikes {
            findings.extend(check_spike(&patterns, &root, number, directory)?);
        }
        Ok(findings)
    });

    match result {
        Ok(findings) if findings.is_empty() => {
            println!(
                "All selected spike blocks are classified, uniquely identified, and exact \
                 authored sources match their directories."
            );
            ExitCode::SUCCESS
        }
        Ok(findings) => {
            for finding in findings {
                eprintln!("{finding}");
            }
            ExitCode::FAILURE
        }
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read(number: u32, text: &str) -> Document {
        read_document(&Patterns::new(), number, text)
    }

    fn block(classification: &str, fence: &str, body: &str) -> String {
        format!("<!-- grass-block: {classification} -->\n{fence}\n{body}\n```\n")
    }

    // --- the empty-scan refusals -----------------------------------------

    #[test]
    fn an_empty_selection_is_refused() {
        // `-Spike @()` in the original selected nothing and printed the success
        // sentence over zero documents.
        let message = selected_spikes(&["6".to_string()])
            .expect_err("a spike outside the corpus must not silently select nothing");
        assert!(message.contains("there is no spike 6"), "{message}");
    }

    #[test]
    fn the_default_selection_is_the_whole_corpus() {
        assert_eq!(selected_spikes(&[]).expect("all").len(), 5);
    }

    #[test]
    fn a_spike_with_no_blocks_and_no_files_is_refused() {
        // The failure this port exists to close: an empty manifest agrees with an
        // empty manifest, so the original reported the spike as consistent.
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("docs")).expect("mkdir");
        fs::create_dir_all(root.join("Spikes/1_Hello_World")).expect("mkdir");
        fs::write(root.join("docs/SPIKE_1.md"), "# Spike 1\n\nProse only.\n").expect("write");

        let findings = check_spike(&Patterns::new(), root, 1, "1_Hello_World").expect("checked");
        assert_eq!(findings.len(), 1, "{findings:?}");
        assert!(findings[0].contains("nothing was compared"), "{findings:?}");
        assert!(
            findings[0].contains("Refusing to report a spike as consistent"),
            "{findings:?}"
        );
        assert!(
            !findings[0].contains("match their directories"),
            "an empty comparison must never borrow the success sentence: {findings:?}"
        );
    }

    #[test]
    fn illustrative_blocks_over_an_empty_directory_are_still_nothing_compared() {
        // Blocks are present, so a check keyed on "did the document have any code
        // block" would pass this. None of them is `authored`, so the manifest
        // comparison still has nothing on either side.
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("docs")).expect("mkdir");
        fs::create_dir_all(root.join("Spikes/2_Sort")).expect("mkdir");
        fs::write(
            root.join("docs/SPIKE_2.md"),
            block("interface id=a", "```lean", "def f := 1"),
        )
        .expect("write");

        let findings = check_spike(&Patterns::new(), root, 2, "2_Sort").expect("checked");
        assert!(findings[0].contains("nothing was compared"), "{findings:?}");
        assert!(
            findings[0].contains("1 fenced code block(s)"),
            "{findings:?}"
        );
    }

    #[test]
    fn a_missing_document_or_directory_says_what_to_do_about_it() {
        let dir = tempfile::tempdir().expect("tempdir");
        let message = check_spike(&Patterns::new(), dir.path(), 1, "1_Hello_World")
            .expect_err("a missing corpus must be an error");
        assert!(
            message.contains("docs/SPIKE_1.md does not exist"),
            "{message}"
        );
        assert!(
            message.contains("Run this from the repository root"),
            "{message}"
        );

        // The other side, independently.
        fs::create_dir_all(dir.path().join("docs")).expect("mkdir");
        fs::write(dir.path().join("docs/SPIKE_1.md"), "").expect("write");
        let message = check_spike(&Patterns::new(), dir.path(), 1, "1_Hello_World")
            .expect_err("a missing spike directory must be an error");
        assert!(
            message.contains("Spikes/1_Hello_World does not exist"),
            "{message}"
        );
    }

    #[test]
    fn one_empty_side_is_an_ordinary_manifest_finding_not_a_refusal() {
        // The refusal is deliberately narrower than "something was empty". A
        // document that declares no authored file while its directory holds one is
        // a manifest difference, and the original's message for that is kept.
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("docs")).expect("mkdir");
        fs::create_dir_all(root.join("Spikes/2_Sort")).expect("mkdir");
        fs::write(root.join("docs/SPIKE_2.md"), "# Spike 2\n\nProse only.\n").expect("write");
        fs::write(root.join("Spikes/2_Sort/Main.lean"), "def main := 1\n").expect("write");

        assert_eq!(
            check_spike(&Patterns::new(), root, 2, "2_Sort").expect("checked"),
            vec![
                "SPIKE_2: authored file manifest differs".to_string(),
                "  only in Spikes/2_Sort: Main.lean".to_string(),
            ]
        );
    }

    // --- classification ----------------------------------------------------

    #[test]
    fn every_classification_form_is_accepted_and_yields_an_identity() {
        let text = [
            block("authored file=Main.lean", "```lean", "def main := 1"),
            block("generated id=g1 derives=nasm", "```text", "90"),
            block("interface id=i1", "```lean", "def f"),
            block("proof-sketch id=p1", "```lean", "theorem t"),
        ]
        .concat();
        let document = read(1, &text);
        assert_eq!(document.blocks, 4);
        assert!(document.findings.is_empty(), "{:?}", document.findings);
        assert_eq!(
            document.authored.get("Main.lean").map(String::as_str),
            Some("def main := 1")
        );
    }

    #[test]
    fn an_unclassified_block_is_reported_and_its_content_is_not_trusted() {
        let text = "```lean\ndef main := 1\n```\n";
        let document = read(3, text);
        assert_eq!(
            document.findings,
            vec!["SPIKE_3: block 1 has no immediate classification"]
        );
        assert!(
            document.authored.is_empty(),
            "an unclassified block claims no file"
        );
    }

    #[test]
    fn a_classification_must_be_on_the_immediately_preceding_line() {
        let text = "<!-- grass-block: interface id=i1 -->\n\n```lean\ndef f\n```\n";
        let document = read(3, text);
        assert_eq!(
            document.findings,
            vec!["SPIKE_3: block 1 has no immediate classification"]
        );
    }

    #[test]
    fn an_unknown_classification_is_reported_verbatim() {
        let text = block("sample id=x", "```lean", "def f");
        assert_eq!(
            read(4, &text).findings,
            vec!["SPIKE_4: invalid classification 'sample id=x'"]
        );
    }

    #[test]
    fn a_generated_block_must_name_its_authority() {
        // `derives=` with only whitespace after it. The pattern's `.+` matches, and
        // the emptiness check is what catches it.
        let text = block("generated id=g1 derives=  ", "```text", "90");
        assert_eq!(
            read(5, &text).findings,
            vec!["SPIKE_5: generated block lacks derives authority"]
        );
    }

    #[test]
    fn an_authored_block_must_be_a_lean_block() {
        let text = block("authored file=Main.lean", "```text", "def main := 1");
        assert_eq!(
            read(1, &text).findings,
            vec!["SPIKE_1: authored Main.lean is not a Lean block"]
        );
    }

    #[test]
    fn a_backslash_path_is_normalised_before_it_becomes_an_identity() {
        let text = block("authored file=Sub\\Main.lean", "```lean", "def main");
        let document = read(1, &text);
        assert!(document.findings.is_empty(), "{:?}", document.findings);
        assert!(document.authored.contains_key("Sub/Main.lean"));
    }

    #[test]
    fn duplicate_paths_and_duplicate_identities_are_both_reported() {
        let text = [
            block("authored file=Main.lean", "```lean", "one"),
            block("authored file=Main.lean", "```lean", "two"),
            block("interface id=i1", "```lean", "a"),
            block("interface id=i1", "```lean", "b"),
        ]
        .concat();
        let document = read(2, &text);
        assert_eq!(
            document.findings,
            vec![
                "SPIKE_2: duplicate authored path Main.lean",
                "SPIKE_2: duplicate block identity authored:Main.lean",
                "SPIKE_2: duplicate block identity interface:i1",
            ]
        );
        assert_eq!(
            document.authored.get("Main.lean").map(String::as_str),
            Some("one"),
            "the first block keeps the path"
        );
    }

    #[test]
    fn an_unterminated_block_abandons_the_rest_of_the_document() {
        let text = concat!(
            "<!-- grass-block: interface id=i1 -->\n",
            "```lean\n",
            "def f\n",
            "<!-- grass-block: interface id=i2 -->\n",
        );
        let document = read(1, text);
        assert_eq!(document.blocks, 1);
        assert_eq!(document.findings, vec!["SPIKE_1: block 1 is unterminated"]);
    }

    #[test]
    fn an_empty_block_has_empty_content() {
        let text = "<!-- grass-block: authored file=Empty.lean -->\n```lean\n```\n";
        let document = read(1, text);
        assert!(document.findings.is_empty(), "{:?}", document.findings);
        assert_eq!(
            document.authored.get("Empty.lean").map(String::as_str),
            Some("")
        );
    }

    #[test]
    fn a_fence_inside_a_block_does_not_open_another_block() {
        let text = concat!(
            "<!-- grass-block: proof-sketch id=p1 -->\n",
            "````\n",
            "```lean\n",
            "nested\n",
            "```\n",
            "````\n",
        );
        // The original's closing test is `^```$`, so the inner lowercase fence
        // closes this block and the outer one opens a second, unclassified block.
        // Reproduced exactly: this is corpus grammar, not an accident of the port.
        let document = read(1, text);
        assert_eq!(document.blocks, 2, "{:?}", document.findings);
    }

    // --- normalisation and content ----------------------------------------

    #[test]
    fn line_endings_and_trailing_newlines_are_normalised_away() {
        assert_eq!(normalize_source("a\r\nb\r\n\r\n"), "a\nb");
        assert_eq!(normalize_source("a\rb\n"), "a\nb");
        assert_eq!(normalize_source("a\n\n\n"), "a");
        assert_eq!(normalize_source(""), "");
        // Leading and interior blank lines are content.
        assert_eq!(normalize_source("\na\n\nb\n"), "\na\n\nb");
    }

    #[test]
    fn content_comparison_is_ordinal() {
        // A zero-width joiner is culture-ignorable, so PowerShell's `-cne` reported
        // these as equal. See the module comment.
        let mut authored = BTreeMap::new();
        authored.insert("Main.lean".to_string(), "def main := 1".to_string());
        let findings = compare_manifest(
            1,
            "Spikes/1_Hello_World",
            "docs/SPIKE_1.md",
            &["Main.lean".to_string()],
            &authored,
            &mut |_| Ok("def main := \u{200d}1".to_string()),
        )
        .expect("compared");
        assert_eq!(
            findings,
            vec!["SPIKE_1: Main.lean differs from its authored block"]
        );
    }

    #[test]
    fn a_matching_manifest_and_content_produce_no_finding() {
        let mut authored = BTreeMap::new();
        authored.insert("Main.lean".to_string(), "def main := 1".to_string());
        let findings = compare_manifest(
            1,
            "Spikes/1_Hello_World",
            "docs/SPIKE_1.md",
            &["Main.lean".to_string()],
            &authored,
            &mut |_| Ok("def main := 1\n".to_string()),
        )
        .expect("compared");
        assert!(findings.is_empty(), "{findings:?}");
    }

    #[test]
    fn a_manifest_difference_names_which_side_each_path_is_on() {
        let mut authored = BTreeMap::new();
        authored.insert("Only_In_Doc.lean".to_string(), "x".to_string());
        authored.insert("Both.lean".to_string(), "x".to_string());
        let findings = compare_manifest(
            4,
            "Spikes/4_Web_Server",
            "docs/SPIKE_4.md",
            &["Both.lean".to_string(), "Only_On_Disk.lean".to_string()],
            &authored,
            &mut |_| Ok("x".to_string()),
        )
        .expect("compared");
        assert_eq!(
            findings,
            vec![
                "SPIKE_4: authored file manifest differs",
                "  only in Spikes/4_Web_Server: Only_On_Disk.lean",
                "  only in docs/SPIKE_4.md: Only_In_Doc.lean",
            ]
        );
    }

    // --- the directory walk -----------------------------------------------

    #[test]
    fn the_walk_finds_nested_lean_files_and_nothing_else() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("Sub")).expect("mkdir");
        fs::write(root.join("Main.lean"), "").expect("write");
        fs::write(root.join("README.md"), "").expect("write");
        fs::write(root.join("Sub/Helper.lean"), "").expect("write");
        assert_eq!(
            lean_files(root).expect("walk"),
            vec!["Main.lean".to_string(), "Sub/Helper.lean".to_string()]
        );
    }

    #[test]
    fn an_empty_directory_yields_no_files() {
        // The other half of the falsification for the refusal above.
        let dir = tempfile::tempdir().expect("tempdir");
        assert!(lean_files(dir.path()).expect("walk").is_empty());
    }

    // --- end to end --------------------------------------------------------

    #[test]
    fn a_consistent_spike_produces_no_findings() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("docs")).expect("mkdir");
        fs::create_dir_all(root.join("Spikes/1_Hello_World")).expect("mkdir");
        fs::write(
            root.join("docs/SPIKE_1.md"),
            format!(
                "# Spike 1\n\n{}{}",
                block(
                    "authored file=Main.lean",
                    "```lean",
                    "def main : IO Unit := pure ()"
                ),
                block(
                    "proof-sketch id=p1",
                    "```lean",
                    "theorem t : True := trivial"
                ),
            ),
        )
        .expect("write");
        fs::write(
            root.join("Spikes/1_Hello_World/Main.lean"),
            "def main : IO Unit := pure ()\r\n",
        )
        .expect("write");

        assert!(check_spike(&Patterns::new(), root, 1, "1_Hello_World")
            .expect("checked")
            .is_empty());
    }

    #[test]
    fn a_drifted_file_is_reported_against_its_path() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("docs")).expect("mkdir");
        fs::create_dir_all(root.join("Spikes/1_Hello_World")).expect("mkdir");
        fs::write(
            root.join("docs/SPIKE_1.md"),
            block("authored file=Main.lean", "```lean", "def main := 1"),
        )
        .expect("write");
        fs::write(
            root.join("Spikes/1_Hello_World/Main.lean"),
            "def main := 2\n",
        )
        .expect("write");

        assert_eq!(
            check_spike(&Patterns::new(), root, 1, "1_Hello_World").expect("checked"),
            vec!["SPIKE_1: Main.lean differs from its authored block"]
        );
    }
}
