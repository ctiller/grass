//! Check that every relative Markdown link in the repository resolves.
//!
//! This is the port of `check-doc-links.ps1`, which was PowerShell-only and
//! therefore unrunnable on a Linux developer host. Nothing about the check is
//! Windows-specific; only its host was.
//!
//! It is a `required_check` on review nominations (`docs/AGENT_REVIEW.md`), which
//! is why the exclusion comment below is written the way it is. The rule it
//! enforces is narrow and worth stating exactly: a Markdown inline link whose
//! target is a *path* -- not a URI with a scheme, not a bare anchor -- must name a
//! file or directory that exists, relative to the document that names it. Anchors
//! are not resolved; a link to `docs/FOUNDATION.md#3` is checked as a link to
//! `docs/FOUNDATION.md`.
//!
//! # The exclusion rule, and why it is written against the relative path
//!
//! Carried verbatim from `check-doc-links.ps1`, because it is the reason that file
//! is shaped the way it is:
//!
//! > The exclusions are matched against the path *relative to the repository
//! > root*, never against the absolute path. Every agent works in a Claude Code
//! > worktree at `<repo>/.claude/worktrees/<name>`, so matching `.claude` against
//! > the absolute path excluded the repository root itself and therefore every
//! > file beneath it: the script reported success over zero documents and exited
//! > 0. A gate that fails open is worse than no gate, and this one is a
//! > `required_check` on review nominations.
//!
//! The original expressed that as six regexes over the relative path -- `^\.git/`,
//! `^\.lake/`, `^\.claude/` and the same three with a leading `/`. Since only
//! `*.md` files are enumerated, the final path component is always a file name, so
//! those six say exactly one thing: skip any document with a *directory* component
//! named `.git`, `.lake` or `.claude`. [`is_excluded_directory`] says that
//! directly, and prunes the walk rather than filtering afterwards.
//!
//! The comparison stays case-insensitive because PowerShell's `-notmatch` is, and
//! a `.Git` directory that the original excluded must not start being scanned by
//! the port.
//!
//! # An audit of nothing is not a clean audit
//!
//! The original printed "All relative links in 0 Markdown files resolve." and
//! exited 0 when it found no documents at all. That is precisely the failure its
//! own header describes -- a gate that fails open -- surviving in the one form the
//! `.claude` fix did not close: run it over an empty tree, or from a directory
//! that is not the repository, and the sentence still reads as assurance.
//!
//! [`verdict`] refuses two empty cases. Zero documents means the walk found
//! nothing to read. Zero examined targets means the documents were read and no
//! relative link was extracted from any of them, which is what a broken
//! [`LINK_PATTERN`] looks like from the outside: every document scanned, every
//! link invisible, no failures, exit 0. Neither is reported as success. See
//! `zero_documents_is_refused` and `zero_examined_targets_is_refused`.
//!
//! # Deliberate departures from the PowerShell
//!
//! - **Deterministic order.** `Get-ChildItem -Recurse` yields filesystem
//!   enumeration order. On NTFS that is stable and roughly alphabetical; on the
//!   ext4 host this port exists for, directory order is a hash order that differs
//!   between machines and can differ between runs, so the failure list a developer
//!   reads was never guaranteed to be reproducible. [`markdown_documents`] sorts,
//!   files before subdirectories, which is the order the Windows runs produced.
//!
//! - **The repository root is the working directory,** with `--root <path>` to
//!   override it. The original used `$PSScriptRoot`, which a compiled
//!   binary has no equivalent of. `.github/workflows/corpus.yml` runs from the
//!   repository root, and the empty-scan refusal above is what catches the case
//!   this replaces.
//!
//! Exit status is 1 on any unresolved link and on either empty scan.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use regex::Regex;

/// Markdown inline links, image links included.
///
/// Carried unchanged from `check-doc-links.ps1`. It deliberately does not
/// understand every link form Markdown admits: reference-style links (`[a][b]`),
/// autolinks (`<https://…>`) and link titles (`[a](b.md "T")`) are all outside it.
/// The last of those is a live defect in the original -- a title lands inside the
/// captured target and the link is then reported missing -- and it is reproduced
/// here rather than fixed, because fixing it silently would change which findings
/// this gate produces. There is no such link in the tree today.
const LINK_PATTERN: &str = r"!?(?:\[[^\]]*\])\(([^)]+)\)";

/// A target that names a URI scheme is somebody else's to check.
///
/// `https:`, `mailto:` and friends. Anchored, so a Windows drive letter (`C:/…`)
/// also matches and is skipped -- the original's behaviour, and harmless: an
/// absolute path is not a relative link.
const SCHEME_PATTERN: &str = r"^[a-zA-Z][a-zA-Z0-9+.-]*:";

/// Directory names whose contents are never documents of this repository.
///
/// `.git` and `.lake` are build and VCS state. `.claude` holds agent worktrees,
/// each of which is a full checkout; scanning them would report another branch's
/// broken links against this one.
const EXCLUDED_DIRECTORIES: &[&str] = &[".git", ".lake", ".claude"];

/// Whether a directory component is pruned from the walk.
///
/// Case-insensitive, matching PowerShell's `-notmatch`. See the module comment.
fn is_excluded_directory(name: &str) -> bool {
    EXCLUDED_DIRECTORIES
        .iter()
        .any(|excluded| name.eq_ignore_ascii_case(excluded))
}

/// Every `*.md` file under `root`, as a `/`-separated path relative to it.
///
/// Files of a directory come before the contents of its subdirectories, and both
/// are sorted, so the failure list is reproducible on every filesystem. See the
/// module comment.
fn markdown_documents(root: &Path) -> Result<Vec<String>, String> {
    let mut found = Vec::new();
    walk(root, "", &mut found)?;
    Ok(found)
}

fn walk(dir: &Path, prefix: &str, found: &mut Vec<String>) -> Result<(), String> {
    let mut files: Vec<String> = Vec::new();
    let mut subdirectories: Vec<String> = Vec::new();
    let entries =
        fs::read_dir(dir).map_err(|err| format!("check-doc-links: {}: {err}", dir.display()))?;
    for entry in entries {
        let entry = entry.map_err(|err| format!("check-doc-links: {}: {err}", dir.display()))?;
        let name = entry.file_name().to_string_lossy().into_owned();
        let file_type = entry
            .file_type()
            .map_err(|err| format!("check-doc-links: {}: {err}", entry.path().display()))?;
        if file_type.is_dir() {
            if !is_excluded_directory(&name) {
                subdirectories.push(name);
            }
        } else if name.to_ascii_lowercase().ends_with(".md") {
            files.push(name);
        }
    }
    // `Sort-Object`'s default is a case-insensitive comparison; the second key
    // makes the result total rather than merely stable, so two names differing only
    // in case cannot swap between runs.
    let by_name = |a: &String, b: &String| {
        a.to_ascii_lowercase()
            .cmp(&b.to_ascii_lowercase())
            .then_with(|| a.cmp(b))
    };
    files.sort_by(by_name);
    subdirectories.sort_by(by_name);

    for name in files {
        found.push(if prefix.is_empty() {
            name
        } else {
            format!("{prefix}/{name}")
        });
    }
    for name in subdirectories {
        let child_prefix = if prefix.is_empty() {
            name.clone()
        } else {
            format!("{prefix}/{name}")
        };
        walk(&dir.join(&name), &child_prefix, found)?;
    }
    Ok(())
}

/// Every inline link target in `text`, exactly as written.
///
/// Trimmed, and with the `<…>` wrapper Markdown allows around a target removed,
/// which is the pair of steps the original performed before splitting off the
/// anchor. The result is what a failure message quotes.
fn link_targets(pattern: &Regex, text: &str) -> Vec<String> {
    pattern
        .captures_iter(text)
        .map(|capture| {
            let target = capture[1].trim();
            match target.strip_prefix('<').and_then(|t| t.strip_suffix('>')) {
                Some(inner) => inner.to_string(),
                None => target.to_string(),
            }
        })
        .collect()
}

/// The path a target names, or `None` when the target is not this gate's business.
///
/// The anchor is split off first, so `docs/A.md#section` is checked as `docs/A.md`
/// and a bare `#section` is skipped along with the empty target. A scheme means an
/// external URI. Percent-escapes are decoded, so a link written `a%20b.md` is
/// checked against the file `a b.md`.
fn target_path(scheme: &Regex, target: &str) -> Option<String> {
    let path = target.split('#').next().unwrap_or("");
    if path.trim().is_empty() || scheme.is_match(path) {
        return None;
    }
    Some(unescape_data_string(path))
}

/// `System.Uri.UnescapeDataString`, to the extent this gate uses it.
///
/// Decodes `%XX`, leaves a malformed escape as written, and -- unlike form
/// decoding -- does not treat `+` as a space. A decoded byte sequence that is not
/// UTF-8 is left as written rather than replaced, so a link is never reported
/// missing under a name nobody typed.
fn unescape_data_string(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'%' && index + 2 < bytes.len() {
            let high = (bytes[index + 1] as char).to_digit(16);
            let low = (bytes[index + 2] as char).to_digit(16);
            if let (Some(high), Some(low)) = (high, low) {
                out.push((high * 16 + low) as u8);
                index += 3;
                continue;
            }
        }
        out.push(bytes[index]);
        index += 1;
    }
    String::from_utf8(out).unwrap_or_else(|_| text.to_string())
}

/// `Join-Path`, which is not `Path::join`.
///
/// `Join-Path 'docs' '/a/b.md'` yields `docs/a/b.md`; `Path::join` would yield
/// `/a/b.md` and resolve a root-relative link against the filesystem root instead
/// of against the document. The original resolved every target through `Join-Path`,
/// so a link written `/docs/A.md` inside `docs/B.md` was checked as
/// `docs/docs/A.md` and reported missing. Concatenation preserves that; switching
/// to `Path::join` would silently start accepting links the gate has been
/// rejecting.
fn join_like_powershell(directory: &Path, relative: &str) -> PathBuf {
    let mut joined = directory.to_string_lossy().into_owned();
    if !joined.is_empty() && !joined.ends_with(['/', '\\']) {
        joined.push(std::path::MAIN_SEPARATOR);
    }
    joined.push_str(relative);
    PathBuf::from(joined)
}

/// What one pass over the tree found.
#[derive(Debug, Default, PartialEq, Eq)]
struct Scan {
    /// How many documents were read.
    documents: usize,
    /// How many relative targets were resolved against the filesystem. Zero over a
    /// non-empty document set means the extraction stopped working.
    examined: usize,
    /// One line per unresolved link, in document order.
    failures: Vec<String>,
}

/// The whole judgement over a completed scan.
///
/// `Ok` carries the line a passing run prints; `Err` carries the text a failing run
/// prints. The two empty-scan refusals come first, because "did this examine
/// anything" is not a finding about the documents and must not be reported as one.
fn verdict(scan: &Scan, root_display: &str) -> Result<String, String> {
    if scan.documents == 0 {
        return Err(format!(
            "check-doc-links: found no Markdown files under {root_display}, so it checked no \
             links.\nRefusing to report that all relative links resolve when none were read: run \
             this from the repository root, or pass --root <path>."
        ));
    }
    if scan.examined == 0 {
        return Err(format!(
            "check-doc-links: read {} Markdown files under {root_display} and extracted no \
             relative link from any of them, so it checked nothing.\nThat is what a broken link \
             pattern looks like from the outside, not a clean repository.",
            scan.documents
        ));
    }
    if !scan.failures.is_empty() {
        let mut message = String::new();
        for failure in &scan.failures {
            let _ = writeln!(message, "{failure}");
        }
        return Err(message.trim_end().to_string());
    }
    Ok(format!(
        "All relative links in {} Markdown files resolve.",
        scan.documents
    ))
}

/// Read every document under `root` and resolve every relative link it names.
fn scan(root: &Path) -> Result<Scan, String> {
    let link = Regex::new(LINK_PATTERN).expect("LINK_PATTERN is a constant");
    let scheme = Regex::new(SCHEME_PATTERN).expect("SCHEME_PATTERN is a constant");
    let documents = markdown_documents(root)?;
    let mut result = Scan {
        documents: documents.len(),
        ..Scan::default()
    };
    for relative in &documents {
        let absolute = root.join(relative.replace('/', std::path::MAIN_SEPARATOR_STR));
        let text = read_utf8(&absolute)?;
        let directory = absolute
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| root.to_path_buf());
        for target in link_targets(&link, &text) {
            let Some(path) = target_path(&scheme, &target) else {
                continue;
            };
            result.examined += 1;
            if !join_like_powershell(&directory, &path).exists() {
                result
                    .failures
                    .push(format!("{relative}: missing target '{target}'"));
            }
        }
    }
    Ok(result)
}

/// `Get-Content -Raw -Encoding utf8`, byte-order mark and all.
fn read_utf8(path: &Path) -> Result<String, String> {
    let text = fs::read_to_string(path)
        .map_err(|err| format!("check-doc-links: {}: {err}", path.display()))?;
    Ok(text.strip_prefix('\u{feff}').unwrap_or(&text).to_string())
}

/// An absolute path a person can read back to themselves.
///
/// `canonicalize` on Windows returns an extended-length path (`\\?\C:\...`). That
/// is correct and is what the API is for, but it is not what anybody typed, and
/// this string appears in a message whose whole job is to say "you ran this
/// somewhere else". The prefix is removed for display only.
fn display_path(root: &Path) -> String {
    let absolute = match root.canonicalize() {
        Ok(absolute) => absolute.display().to_string(),
        Err(_) => return root.display().to_string(),
    };
    match absolute.strip_prefix(r"\\?\") {
        Some(plain) => plain.to_string(),
        None => absolute,
    }
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let root = match arguments.as_slice() {
        [] => PathBuf::from("."),
        [flag, path] if flag == "--root" => PathBuf::from(path),
        _ => {
            eprintln!(
                "check-doc-links: usage: doc-links [--root <path>]\nThe root defaults to the \
                 working directory."
            );
            return ExitCode::FAILURE;
        }
    };
    let display = display_path(&root);
    let result = scan(&root).and_then(|scanned| verdict(&scanned, &display));
    match result {
        Ok(message) => {
            println!("{message}");
            ExitCode::SUCCESS
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

    fn targets(text: &str) -> Vec<String> {
        let pattern = Regex::new(LINK_PATTERN).expect("pattern");
        link_targets(&pattern, text)
    }

    fn path_of(target: &str) -> Option<String> {
        let scheme = Regex::new(SCHEME_PATTERN).expect("pattern");
        target_path(&scheme, target)
    }

    // --- the empty-scan refusals -----------------------------------------

    #[test]
    fn zero_documents_is_refused() {
        // The failure this port exists to close. `check-doc-links.ps1` printed
        // "All relative links in 0 Markdown files resolve." and exited 0.
        let message = verdict(&Scan::default(), "/tmp/empty")
            .expect_err("a scan that read nothing must not report success");
        assert!(message.contains("found no Markdown files"), "{message}");
        assert!(
            message.contains("Refusing to report that all relative links resolve"),
            "{message}"
        );
        assert!(
            !message.contains("resolve."),
            "an empty scan must never borrow the success sentence: {message}"
        );
    }

    #[test]
    fn zero_examined_targets_is_refused() {
        let scanned = Scan {
            documents: 60,
            examined: 0,
            failures: Vec::new(),
        };
        let message = verdict(&scanned, "/repo")
            .expect_err("documents with no extracted links must not report success");
        assert!(message.contains("extracted no relative link"), "{message}");
        assert!(message.contains("read 60 Markdown files"), "{message}");
    }

    #[test]
    fn a_scan_that_examined_something_and_found_nothing_passes() {
        let scanned = Scan {
            documents: 60,
            examined: 214,
            failures: Vec::new(),
        };
        assert_eq!(
            verdict(&scanned, "/repo").expect("clean"),
            "All relative links in 60 Markdown files resolve."
        );
    }

    #[test]
    fn failures_are_reported_one_per_line_in_order() {
        let scanned = Scan {
            documents: 2,
            examined: 3,
            failures: vec![
                "README.md: missing target 'docs/GONE.md'".to_string(),
                "docs/A.md: missing target 'B.md#x'".to_string(),
            ],
        };
        let message = verdict(&scanned, "/repo").expect_err("failures must fail the gate");
        assert_eq!(
            message,
            "README.md: missing target 'docs/GONE.md'\ndocs/A.md: missing target 'B.md#x'"
        );
    }

    // --- extraction --------------------------------------------------------

    #[test]
    fn inline_and_image_links_are_extracted_and_unwrapped() {
        assert_eq!(
            targets("see [the vision](docs/VISION.md) and ![img](a/b.png)"),
            vec!["docs/VISION.md".to_string(), "a/b.png".to_string()]
        );
        assert_eq!(
            targets("[a](<docs/with space.md>)"),
            vec!["docs/with space.md"]
        );
        assert_eq!(targets("[a](  docs/A.md  )"), vec!["docs/A.md"]);
        // An empty label still forms a link; the original matched `\[[^\]]*\]`.
        assert_eq!(targets("[](x.md)"), vec!["x.md"]);
    }

    #[test]
    fn forms_the_original_never_understood_are_still_not_understood() {
        // Reference links and autolinks produce no target, as before.
        assert!(targets("[a][b]\n\n[b]: docs/A.md").is_empty());
        assert!(targets("<https://example.invalid>").is_empty());
        // A link title lands inside the target. This is the original's defect,
        // reproduced deliberately; see LINK_PATTERN.
        assert_eq!(targets(r#"[a](b.md "T")"#), vec![r#"b.md "T""#]);
    }

    #[test]
    fn anchors_schemes_and_empty_targets_are_skipped() {
        assert_eq!(path_of("docs/A.md#section"), Some("docs/A.md".to_string()));
        assert_eq!(path_of("#section"), None);
        assert_eq!(path_of("   "), None);
        assert_eq!(path_of("https://example.invalid/x"), None);
        assert_eq!(path_of("mailto:someone@example.invalid"), None);
        assert_eq!(path_of("C:/Users/x/A.md"), None);
        // Not a scheme: a colon after a non-leading digit-started segment.
        assert_eq!(path_of("A.md"), Some("A.md".to_string()));
    }

    #[test]
    fn percent_escapes_are_decoded_and_malformed_ones_are_left_alone() {
        assert_eq!(unescape_data_string("a%20b.md"), "a b.md");
        assert_eq!(unescape_data_string("a%2Fb.md"), "a/b.md");
        assert_eq!(unescape_data_string("100%.md"), "100%.md");
        assert_eq!(unescape_data_string("a%zz.md"), "a%zz.md");
        // Form decoding would turn this into a space. `UnescapeDataString` does not.
        assert_eq!(unescape_data_string("a+b.md"), "a+b.md");
    }

    // --- resolution --------------------------------------------------------

    #[test]
    fn a_root_relative_target_is_joined_not_rooted() {
        // `Path::join` would return `/docs/A.md` and check the filesystem root.
        let joined = join_like_powershell(Path::new("/repo/docs"), "/docs/A.md");
        assert!(
            joined.to_string_lossy().contains("repo"),
            "{}",
            joined.display()
        );
        assert!(joined.to_string_lossy().ends_with("/docs/A.md"));
    }

    #[test]
    fn a_trailing_separator_is_not_doubled() {
        let joined = join_like_powershell(Path::new("docs/"), "A.md");
        assert_eq!(joined.to_string_lossy(), "docs/A.md");
    }

    // --- the walk ----------------------------------------------------------

    #[test]
    fn build_and_worktree_directories_are_pruned_case_insensitively() {
        assert!(is_excluded_directory(".git"));
        assert!(is_excluded_directory(".Git"));
        assert!(is_excluded_directory(".lake"));
        assert!(is_excluded_directory(".claude"));
        assert!(!is_excluded_directory("docs"));
        assert!(!is_excluded_directory("git"));
        assert!(!is_excluded_directory(".gitignore"));
    }

    #[test]
    fn the_walk_finds_documents_in_a_reproducible_order() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("docs")).expect("mkdir");
        fs::create_dir_all(root.join(".claude/worktrees/w")).expect("mkdir");
        fs::create_dir_all(root.join(".lake/build")).expect("mkdir");
        fs::write(root.join("README.md"), "").expect("write");
        fs::write(root.join("CONTRIBUTING.md"), "").expect("write");
        fs::write(root.join("notes.txt"), "").expect("write");
        fs::write(root.join("docs/VISION.md"), "").expect("write");
        fs::write(root.join("docs/AGENT_BUS.md"), "").expect("write");
        fs::write(root.join(".claude/worktrees/w/README.md"), "").expect("write");
        fs::write(root.join(".lake/build/NOTES.md"), "").expect("write");

        assert_eq!(
            markdown_documents(root).expect("walk"),
            vec![
                "CONTRIBUTING.md".to_string(),
                "README.md".to_string(),
                "docs/AGENT_BUS.md".to_string(),
                "docs/VISION.md".to_string(),
            ]
        );
    }

    #[test]
    fn a_displayed_root_is_not_an_extended_length_path() {
        let dir = tempfile::tempdir().expect("tempdir");
        let shown = display_path(dir.path());
        assert!(!shown.starts_with(r"\\?\"), "{shown}");
        // A path that cannot be canonicalised is shown as written rather than
        // suppressed; the message is about where the user was.
        assert_eq!(display_path(Path::new("no/such/place")), "no/such/place");
    }

    #[test]
    fn an_empty_tree_yields_no_documents() {
        // The other half of the falsification: the walk really does return nothing,
        // so `verdict` really does meet the empty case above.
        let dir = tempfile::tempdir().expect("tempdir");
        fs::create_dir_all(dir.path().join("docs")).expect("mkdir");
        assert!(markdown_documents(dir.path()).expect("walk").is_empty());
    }

    // --- end to end over a constructed tree --------------------------------

    #[test]
    fn a_broken_link_is_reported_against_the_document_that_names_it() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("docs")).expect("mkdir");
        fs::write(root.join("docs/A.md"), "").expect("write");
        fs::write(
            root.join("README.md"),
            "[here](docs/A.md) [gone](docs/GONE.md) [ext](https://example.invalid) [anchor](#x)\n",
        )
        .expect("write");

        let scanned = scan(root).expect("scan");
        assert_eq!(scanned.documents, 2);
        assert_eq!(
            scanned.examined, 2,
            "the external link and the anchor are not resolved"
        );
        assert_eq!(
            scanned.failures,
            vec!["README.md: missing target 'docs/GONE.md'".to_string()]
        );
    }

    #[test]
    fn a_link_is_resolved_against_its_own_directory_and_keeps_its_anchor_in_the_message() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("docs")).expect("mkdir");
        fs::write(
            root.join("docs/A.md"),
            "[up](../README.md#top) [side](B.md#x)\n",
        )
        .expect("write");
        fs::write(root.join("README.md"), "[a](docs/A.md)\n").expect("write");

        let scanned = scan(root).expect("scan");
        assert_eq!(
            scanned.failures,
            vec!["docs/A.md: missing target 'B.md#x'".to_string()],
            "../README.md resolves from docs/, and the anchor stays in the quoted target"
        );
    }

    #[test]
    fn a_directory_target_resolves() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("Spikes")).expect("mkdir");
        fs::write(root.join("README.md"), "[spikes](Spikes)\n").expect("write");
        assert!(scan(root).expect("scan").failures.is_empty());
    }
}
