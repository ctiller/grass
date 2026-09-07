//! Check that strong implementation-comment claims name their enforcement.
//!
//! Scope: module comments and the docstrings of definitions, structures, classes,
//! inductives -- and theorems. A theorem's own docstring was meant to be exempt, on
//! the grounds that the theorem beneath it *is* the enforcement, and the Python
//! this replaces said so for a long time while never implementing it: the
//! `SELF_NAMING` pattern was defined and never used. A reviewer found the dead
//! constant.
//!
//! The exemption is not reinstated. It would be the wrong direction: a theorem's
//! docstring routinely claims more than its statement proves -- that is how
//! `decodeInsn_toBytes` came to be described as evidence about x86 -- and the
//! check is cheap. This comment describes what the code does.
//!
//! docs/MEMORY_IMPLEMENTATION_PLAN.md section 3.10:
//!
//! > Any implementation comment using "ensures", "prevents", "cannot", "only", or
//! > "preserves" must name the enforcing type or theorem. If it cannot name one, it
//! > must be rewritten as an intended invariant or an open obligation.
//!
//! Four adversarial review rounds each found a docstring asserting a property the
//! code did not have -- including one naming a theorem that did not exist, in the
//! file whose own comment states this rule. Mechanism-shaped prose reads as
//! verification and is not, so the rule needs a checker rather than a convention.
//!
//! The check is deliberately shallow. It cannot tell whether a named theorem proves
//! what the sentence claims; it can tell that the sentence names something the build
//! knows about, which is the difference between a claim that can be chased and one
//! that cannot.
//!
//! That second half used to be false. The tool never touched a Lean environment --
//! it looked for a backticked identifier and stopped -- so any invented name
//! satisfied it. A reviewer passed the audit with a sentence claiming the encoder
//! "ensures" and "prevents", backed by
//! `encodeMem_is_canonical_and_injective_over_all_addresses`, which does not exist;
//! the identical sentence with the backticks removed failed. That is precisely the
//! defect this file's own header cites as its reason for existing. Names are now
//! checked against `Tools/DeclNames.lean`, which prints every declaration the build
//! knows. A sentence that hedges -- "intended", "not enforced", "owes",
//! "open obligation", and the like -- is exempt, because saying a property is not yet
//! mechanised is exactly the honest alternative the rule asks for.
//!
//! Exit status is 1 if any claim is unbacked.
//!
//! # One deliberate departure from the Python
//!
//! `Tools/DocstringAudit.py` skipped a root that was not a directory and, having
//! scanned nothing, printed its success line and exited 0. Run from the wrong
//! working directory -- or against a sparse checkout, or after a rename -- it
//! reported a clean audit of zero files, which is how a gate stops gating without
//! anyone noticing. This port refuses to do that: scanning no files is a failure,
//! reported as one, before the six-minute Lean run that would otherwise be the
//! first thing to fail. See `run`.
//!
//! # One difference that is not a departure
//!
//! The Python emitted its heading and its closing count with `print`, and each
//! finding with `sys.stdout.buffer.write`, which bypasses the text layer's
//! buffer. On a terminal that reads correctly; through a pipe -- which is every
//! CI invocation -- the text layer holds the heading until exit and the findings
//! overtake it, so the report arrives with its heading at the bottom. Confirmed
//! by running the Python twice over the same tree, once plain and once under
//! `-u`: the unbuffered run matched this port line for line, and the buffered one
//! carried the same lines in a scrambled order. This port writes the order a
//! reader expects.

use std::collections::HashSet;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::{Command, ExitCode};
use std::sync::OnceLock;

use regex::Regex;

/// Deliberately narrow. The designer's rule names "ensures", "prevents", "cannot",
/// "only", and "preserves"; the last two occur constantly in ordinary descriptive
/// English ("the only fault position", "a value that is never live") and flagging
/// every one buries the signal. What is kept are the words that assert a mechanism
/// rather than describe a value, plus "only" in its guarantee-shaped phrasings.
///
/// The tool therefore under-reports by construction. It is a net for the specific
/// drift four review rounds found -- a definition or module comment asserting an
/// enforcement it does not name -- not a proof that no comment overclaims.
const CLAIM_WORDS: &[&str] = &[
    "ensures",
    "ensuring",
    "prevents",
    "preventing",
    "cannot",
    "preserves",
    "guarantees",
    "makes it impossible",
    "is enforced",
    "only if",
    "only when",
];

/// A sentence that says a property is aspirational, absent, or owed elsewhere is
/// not making a mechanised claim, and the rule explicitly permits it.
const HEDGES: &[&str] = &[
    "intended",
    "not enforced",
    "cannot be made",
    "owes",
    "owed",
    "open obligation",
    "used to",
    "an earlier",
    "M2",
    "M3",
    "M4",
    "M5",
    "M6",
    "M7",
    "M8",
    "M9",
    "M10",
    "no arrangement",
    "is not the check",
    "not by itself",
    "on its own",
    "nothing here",
    "cannot tell",
    "is not that",
    "not something",
    "no way to",
    "unrepresentable",
    // "X cannot do Y" is a statement of limitation, which is the honest
    // alternative the rule asks for rather than the drift it targets.
    "cannot state",
    "cannot be demonstrated",
    "cannot read",
    "cannot fault",
    "cannot lawfully",
    "cannot coexist",
    "cannot be checked",
    "cannot introduce",
    "cannot enforce",
    "cannot answer",
    "cannot express",
    "cannot know",
    "cannot be erased or masked",
];

/// Hedges match as whole words, not as bare substrings.
///
/// As substrings they matched inside ordinary vocabulary: "owed" inside
/// `Allowed`, and the milestone labels "M3", "M6" and "M8" inside `imm32`,
/// `imm64` and `imm8`. A reviewer found three sentences exempted for no reason
/// but the letters in an operand size, which in an x86 tree was only going to
/// get worse.
///
/// The milestone labels stay. They refer to the milestones of
/// `docs/MEMORY_IMPLEMENTATION_PLAN.md`, so a sentence naming one is describing
/// work that is not built yet -- which is a hedge in exactly the sense this list
/// means. The reviewer read them as review scratch and the Python briefly agreed;
/// both were wrong, and removing them would have suppressed a legitimate
/// exemption in `Grass/Memory/Event.lean`.
fn hedge_re() -> &'static Regex {
    static RE: OnceLock<Regex> = OnceLock::new();
    RE.get_or_init(|| {
        let alternation = HEDGES
            .iter()
            .map(|h| format!(r"\b{}\b", regex::escape(&h.to_lowercase())))
            .collect::<Vec<_>>()
            .join("|");
        Regex::new(&alternation).expect("hedge alternation is built from escaped literals")
    })
}

/// Which unresolved names are worth reporting.
///
/// Requiring *every* backticked identifier to resolve over-fires: `RAX`,
/// `INC`, `REX.X`, `SizeOfProlog`, `UWOP_SAVE_XMM128` and `cl.exe` are correct
/// technical writing, and so are `w.bits` and `d.space`, which name a binder's
/// field. Sixteen such sentences fail that rule and none of them is drift.
///
/// Requiring only that *something* resolves is what a reviewer defeated: naming
/// the function a sentence is about -- normal, good writing -- masks an invented
/// theorem name in the same sentence. "`encode` ensures every address has one
/// encoding, as proved by `encodeMem_is_canonical_and_injective_over_all_addresses`"
/// passed, while the same sentence without `encode` failed.
///
/// So this matches the shape of a Lean declaration name rather than the shape of
/// an identifier: lowercase-initial with at least one underscore-separated part,
/// which is the convention every theorem in this repository follows and which
/// none of the false positives above has. It is a heuristic and is stated as one.
/// It does not catch an invented `camelCase` name, and an author who wants to
/// fabricate enforcement can still do it; what it catches is the form that
/// fabrication actually takes, because a fabricated *theorem* is what a claim
/// cites.
fn lean_style_name_re() -> &'static Regex {
    static RE: OnceLock<Regex> = OnceLock::new();
    RE.get_or_init(|| {
        Regex::new(r"^[a-z][A-Za-z0-9']*(_[A-Za-z0-9'][A-Za-z0-9']*)+$").expect("literal pattern")
    })
}

/// A backticked identifier is the "names the enforcing type or theorem" part.
fn ident_re() -> &'static Regex {
    static RE: OnceLock<Regex> = OnceLock::new();
    RE.get_or_init(|| Regex::new(r"`([A-Za-z_][A-Za-z0-9_.?!']*)`").expect("literal pattern"))
}

/// Section references and prose in backticks are not identifiers.
///
/// Carried over from the Python unchanged, and unreachable there for the same
/// reason it is unreachable here: it is applied to the *capture* of `ident_re`,
/// whose character class admits neither `/`, nor `§`, nor whitespace, so none of
/// its three alternatives can ever match. It is kept because removing a filter is
/// a behaviour change and this port's job is not to make those, and because
/// deleting it would hide a real finding rather than record it. See the report
/// note on dead constants -- this is the second one this tool has carried.
fn not_ident_re() -> &'static Regex {
    static RE: OnceLock<Regex> = OnceLock::new();
    RE.get_or_init(|| Regex::new(r"^(docs/|§|[a-z]+\s)").expect("literal pattern"))
}

/// Every name the build knows, plus every dotted suffix of one.
///
/// Suffixes because a docstring names a declaration the way a reader would --
/// `writeBack.w32_clears_high`, not `Grass.ISA.X86.writeBack.w32_clears_high` --
/// and demanding the fully qualified form would push authors towards naming
/// nothing.
///
/// A missing oracle is a failure, not a skip: an audit that passes because it
/// could not obtain the name list is worse than no audit, which is the mistake
/// this function was added to correct.
fn declaration_names() -> Result<HashSet<String>, String> {
    let output = Command::new("lake")
        .args(["env", "lean", "Tools/DeclNames.lean"])
        .output()
        .map_err(|err| {
            format!("could not obtain the declaration list from Tools/DeclNames.lean:\n{err}")
        })?;

    // `text=True, encoding="utf-8", errors="replace"` in the Python; lossy decoding
    // substitutes the same U+FFFD, and the universal-newline translation that came
    // with it is absorbed by `py_splitlines`.
    let stdout = String::from_utf8_lossy(&output.stdout);
    if !output.status.success() {
        let combined = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
        let capped: String = py_strip(&combined).chars().take(2000).collect();
        return Err(format!(
            "could not obtain the declaration list from Tools/DeclNames.lean:\n{capped}"
        ));
    }

    let mut known: HashSet<String> = HashSet::new();
    for line in py_splitlines(&stdout) {
        let name = py_strip(line);
        if name.is_empty() || name.contains(' ') {
            continue;
        }
        let mut suffix = name;
        loop {
            known.insert(suffix.to_string());
            match suffix.find('.') {
                Some(dot) => suffix = &suffix[dot + 1..],
                None => break,
            }
        }
    }
    // Sorts are not constants, so a sentence naming only `Prop` or `Type` would
    // otherwise be reported as naming nothing.
    for sort in ["Prop", "Type", "Sort"] {
        known.insert(sort.to_string());
    }
    if known.len() < 1000 {
        return Err(format!(
            "declaration list has only {} entries, which cannot be right; refusing to report a \
             clean audit against it",
            known.len()
        ));
    }
    Ok(known)
}

/// Split a docstring block into sentences.
///
/// Split on sentence ends only. A semicolon joins a claim to the clause that
/// names its enforcement, so splitting there would report the claim as unbacked
/// while the name sits in the next fragment.
///
/// The Python spelled the split as `re.split(r"(?<=[.])\s+", text)`. The `regex`
/// crate has no lookbehind, so the same rule is applied directly: a run of
/// whitespace is a boundary exactly when the character before it is a full stop.
/// Positions inside such a run cannot start a second boundary, because the
/// character before them is whitespace rather than `.`, which is why consuming
/// the whole run reproduces the greedy `\s+`.
fn sentences(block: &str) -> Vec<String> {
    let text = py_splitlines(block)
        .into_iter()
        .map(py_strip)
        .collect::<Vec<_>>()
        .join(" ");

    let mut out = Vec::new();
    let mut piece_start = 0usize;
    let mut previous: Option<char> = None;
    let mut chars = text.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if is_py_space(ch) && previous == Some('.') {
            out.push(&text[piece_start..idx]);
            while let Some(&(_, next)) = chars.peek() {
                if is_py_space(next) {
                    chars.next();
                } else {
                    break;
                }
            }
            piece_start = chars.peek().map_or(text.len(), |&(next, _)| next);
            previous = None;
            continue;
        }
        previous = Some(ch);
    }
    out.push(&text[piece_start..]);

    out.into_iter()
        .map(py_strip)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .collect()
}

/// Yield (line number, text) for every `/-- ... -/` and `/-! ... -/` block.
fn doc_blocks(source: &str) -> Vec<(usize, &str)> {
    static RE: OnceLock<Regex> = OnceLock::new();
    let re = RE.get_or_init(|| Regex::new(r"(?s)/-[-!](.*?)-/").expect("literal pattern"));
    re.captures_iter(source)
        .map(|caps| {
            let whole = caps.get(0).expect("group 0 always participates");
            let line = source[..whole.start()].matches('\n').count() + 1;
            (
                line,
                caps.get(1).expect("group 1 always participates").as_str(),
            )
        })
        .collect()
}

/// Report every strong claim in `source` that names nothing the build knows.
///
/// `path` is the POSIX-shaped path used in the finding text, so a finding reads
/// the same on Windows as it does on the Linux runner that gates the branch.
fn check(path: &str, source: &str, known: &HashSet<String>) -> Vec<String> {
    let mut findings = Vec::new();
    for (line, block) in doc_blocks(source) {
        for sentence in sentences(block) {
            let lowered = sentence.to_lowercase();
            if !CLAIM_WORDS.iter().any(|word| lowered.contains(word)) {
                continue;
            }
            if hedge_re().is_match(&lowered) {
                continue;
            }
            // A passage quoted from a normative document is that document's
            // claim, not this module's. It is cited, which is the point.
            if sentence.contains("docs/") && sentence.contains('"') {
                continue;
            }
            let named: Vec<&str> = ident_re()
                .captures_iter(&sentence)
                .map(|caps| caps.get(1).expect("group 1 always participates").as_str())
                .filter(|ident| !not_ident_re().is_match(ident))
                .collect();
            let resolved = named.iter().any(|ident| known.contains(*ident));
            // An unresolved name that *looks like a Lean declaration* is the
            // attack; an unresolved `RAX` or `INC` is ordinary prose. See
            // `lean_style_name_re`.
            let invented: Vec<&str> = named
                .iter()
                .copied()
                .filter(|ident| !known.contains(*ident) && lean_style_name_re().is_match(ident))
                .collect();
            if !invented.is_empty() {
                findings.push(format!(
                    "{path}:{line}: claim names {}, which look like declarations and are not in \
                     the build: {}",
                    py_list_repr(&invented),
                    py_repr(&sentence)
                ));
            } else if !named.is_empty() && !resolved {
                findings.push(format!(
                    "{path}:{line}: claim names {} but the build knows no such declaration: {}",
                    py_list_repr(&named),
                    py_repr(&sentence)
                ));
            } else if named.is_empty() {
                findings.push(format!(
                    "{path}:{line}: claim names no enforcing type or theorem: {}",
                    py_repr(&sentence)
                ));
            }
        }
    }
    findings
}

/// Every `*.lean` file under `root`, as (POSIX path, absolute path) in the order
/// the Python reported them.
///
/// The Python sorted `Path` objects, and `pathlib` compares them component by
/// component rather than as flat strings. The difference is visible in this very
/// tree: `Grass/Process/Acceptance.lean` sorts *before* `Grass/Process.lean`,
/// because the component `Process` is a prefix of `Process.lean`, where a flat
/// string comparison puts `.` (0x2E) before `/` (0x2F) and reverses the pair.
/// A differential against the Python found exactly that one transposition, which
/// is why the comparison below is over components and not over the joined path.
///
/// Comparison is case-sensitive, as it is on the Linux runner that gates this
/// branch. Windows `pathlib` lowercases each component first; no two names in
/// this tree differ only by case, so the two agree here, and where they could
/// ever disagree the runner's answer is the one that matters.
fn lean_files(root: &Path, prefix: &str) -> Result<Vec<(String, std::path::PathBuf)>, String> {
    let mut found = Vec::new();
    let mut stack = vec![(root.to_path_buf(), prefix.to_string())];
    while let Some((dir, dir_posix)) = stack.pop() {
        let entries = fs::read_dir(&dir).map_err(|err| format!("{}: {err}", dir.display()))?;
        for entry in entries {
            let entry = entry.map_err(|err| format!("{}: {err}", dir.display()))?;
            let name = entry.file_name().to_string_lossy().into_owned();
            let posix = format!("{dir_posix}/{name}");
            let file_type = entry
                .file_type()
                .map_err(|err| format!("{}: {err}", entry.path().display()))?;
            if file_type.is_dir() {
                stack.push((entry.path(), posix));
            } else if name.ends_with(".lean") {
                found.push((posix, entry.path()));
            }
        }
    }
    found.sort_by(|a, b| a.0.split('/').cmp(b.0.split('/')));
    Ok(found)
}

/// Read a Lean source the way Python's `Path.read_text` did.
///
/// `read_text` opens in text mode, so `\r\n` and a lone `\r` both arrive as
/// `\n`. The line numbers in a finding, and the sentence text quoted beside
/// them, both depend on that having happened.
fn read_source(path: &Path) -> Result<String, String> {
    let bytes = fs::read(path).map_err(|err| format!("{}: {err}", path.display()))?;
    let text = String::from_utf8(bytes).map_err(|err| format!("{}: {err}", path.display()))?;
    if !text.contains('\r') {
        return Ok(text);
    }
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '\r' {
            if chars.peek() == Some(&'\n') {
                chars.next();
            }
            out.push('\n');
        } else {
            out.push(ch);
        }
    }
    Ok(out)
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        // `sys.exit(message)` in the Python: the message on stderr, status 1.
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

/// Every `*.lean` file under every root, in the order the findings are reported.
///
/// A root that is not a directory is skipped rather than refused, exactly as the
/// Python skipped it. What changes is what happens afterwards: the caller treats
/// an empty result as a failure instead of as a clean tree.
fn collect_files(roots: &[(&str, &Path)]) -> Result<Vec<(String, std::path::PathBuf)>, String> {
    let mut files = Vec::new();
    for (prefix, root) in roots {
        if !root.is_dir() {
            continue;
        }
        files.extend(lean_files(root, prefix)?);
    }
    Ok(files)
}

fn run() -> Result<ExitCode, String> {
    // `Tests/` is excluded: fixture comments describe values ("an identity that
    // is never live"), not mechanisms, and the fixtures are themselves the
    // evidence a claim would point at.
    let roots: &[(&str, &Path)] = &[("Grass", Path::new("Grass"))];

    // The file list is gathered before the declaration list, which the Python did
    // the other way round. A wrong working directory breaks both, and "scanned no
    // files" is the diagnosis; reaching it first also means the failure does not
    // wait on a full Lean elaboration to arrive.
    let files = collect_files(roots)?;
    if files.is_empty() {
        let names: Vec<&str> = roots.iter().map(|(prefix, _)| *prefix).collect();
        return Err(zero_files_message(&names));
    }

    let known = declaration_names()?;
    let mut findings = Vec::new();
    for (posix, path) in &files {
        findings.extend(check(posix, &read_source(path)?, &known));
    }

    if !findings.is_empty() {
        println!("docstring audit: claims that name nothing enforcing them\n");
        for finding in &findings {
            println!("  {finding}");
        }
        println!(
            "\n{} unbacked claim(s). Name the type or theorem, or rewrite as an intended \
             invariant or open obligation.",
            findings.len()
        );
        return Ok(ExitCode::FAILURE);
    }
    println!("docstring audit: every strong claim names an enforcing type or theorem");
    Ok(ExitCode::SUCCESS)
}

/// The message behind this port's one deliberate departure from the Python.
///
/// A tree-walking auditor run from the wrong directory finds nothing, reports
/// nothing, and exits 0, which is indistinguishable from a clean tree. Naming the
/// working directory in the message is what turns the failure into a diagnosis.
fn zero_files_message(roots: &[&str]) -> String {
    let cwd = std::env::current_dir()
        .map(|p| p.display().to_string())
        .unwrap_or_else(|err| format!("<unavailable: {err}>"));
    format!(
        "docstring audit: found no .lean files under {} from {cwd}, so it audited nothing.\n\
         Refusing to report a clean audit of an empty scan: run this from the repository root.",
        roots.join(", ")
    )
}

// ---------------------------------------------------------------------------
// Python-shaped text primitives.
//
// The finding lines are compared against `Tools/DocstringAudit.py` output during
// review, so the quoting, the whitespace classification and the line splitting
// all have to be Python's rather than Rust's.
// ---------------------------------------------------------------------------

/// Python's `str.isspace`: Rust's `White_Space` plus the four C0 file/group
/// separators, which Python counts as whitespace and Unicode does not.
fn is_py_space(ch: char) -> bool {
    ch.is_whitespace() || ('\u{1c}'..='\u{1f}').contains(&ch)
}

/// Python's `str.strip()` with no argument.
fn py_strip(text: &str) -> &str {
    text.trim_matches(is_py_space)
}

/// Python's `str.splitlines()`, which splits on rather more than `\n`.
fn py_splitlines(text: &str) -> Vec<&str> {
    const BREAKS: &[char] = &[
        '\n', '\r', '\u{b}', '\u{c}', '\u{1c}', '\u{1d}', '\u{1e}', '\u{85}', '\u{2028}',
        '\u{2029}',
    ];
    let mut lines = Vec::new();
    let mut start = 0usize;
    let mut chars = text.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if !BREAKS.contains(&ch) {
            continue;
        }
        lines.push(&text[start..idx]);
        if ch == '\r' && chars.peek().map(|&(_, next)| next) == Some('\n') {
            chars.next();
        }
        start = chars.peek().map_or(text.len(), |&(next, _)| next);
    }
    if start < text.len() {
        lines.push(&text[start..]);
    }
    lines
}

/// Python's `repr()` for a `str`.
///
/// Single quotes unless the text contains one and no double quote, backslash
/// escapes for the quote character and the three usual controls, and `\xNN` /
/// `\uXXXX` for anything Python calls unprintable.
fn py_repr(text: &str) -> String {
    let quote = if text.contains('\'') && !text.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut out = String::with_capacity(text.len() + 2);
    out.push(quote);
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            c if is_py_printable(c) => out.push(c),
            c if (c as u32) < 0x100 => {
                let _ = write!(out, "\\x{:02x}", c as u32);
            }
            c if (c as u32) < 0x10000 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => {
                let _ = write!(out, "\\U{:08x}", c as u32);
            }
        }
    }
    out.push(quote);
    out
}

/// Python's `repr()` for a list of `str`, which is how a finding names the
/// identifiers it objected to.
fn py_list_repr(items: &[&str]) -> String {
    let inner = items
        .iter()
        .map(|item| py_repr(item))
        .collect::<Vec<_>>()
        .join(", ");
    format!("[{inner}]")
}

/// Python's `str.isprintable()`, to the precision this corpus needs.
///
/// Python calls a character unprintable when its category is `Cc`, `Cf`, `Cs`,
/// `Co`, `Cn`, `Zl`, `Zp` or `Zs` -- except U+0020, which is printable. Rust's
/// standard library exposes no category table, so the separators and format
/// controls that can plausibly reach a Lean docstring are listed and everything
/// else non-ASCII is treated as printable. Nothing outside this list has been
/// observed in the corpus; a character that escapes it is quoted literally rather
/// than as `\uXXXX`, which is a cosmetic difference in a finding's quoted
/// sentence and not a difference in what is flagged.
fn is_py_printable(ch: char) -> bool {
    if ch.is_ascii() {
        return (' '..='~').contains(&ch);
    }
    !matches!(ch,
        '\u{80}'..='\u{a0}'          // C1 controls and NO-BREAK SPACE
        | '\u{ad}'                   // SOFT HYPHEN (Cf)
        | '\u{600}'..='\u{605}'      // Arabic number signs (Cf)
        | '\u{61c}'                  // ARABIC LETTER MARK (Cf)
        | '\u{1680}'                 // OGHAM SPACE MARK (Zs)
        | '\u{180e}'                 // MONGOLIAN VOWEL SEPARATOR (Cf)
        | '\u{2000}'..='\u{200f}'    // Zs run, then the zero-width/bidi marks
        | '\u{2028}'..='\u{202e}'    // line/paragraph separators, bidi overrides
        | '\u{205f}'..='\u{2064}'    // MEDIUM MATHEMATICAL SPACE onwards (Zs, Cf)
        | '\u{2066}'..='\u{206f}'    // bidi isolates and deprecated format chars
        | '\u{3000}'                 // IDEOGRAPHIC SPACE (Zs)
        | '\u{feff}'                 // ZERO WIDTH NO-BREAK SPACE (Cf)
        | '\u{e0000}'..='\u{e007f}') // tag characters (Cf)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn known_set(names: &[&str]) -> HashSet<String> {
        names.iter().map(|n| (*n).to_string()).collect()
    }

    // --- the rule that decides a violation -------------------------------

    #[test]
    fn claim_naming_a_known_declaration_is_clean() {
        let known = known_set(&["encode_is_injective"]);
        let source = "/-- The encoder ensures one encoding per address, by \
                      `encode_is_injective`. -/\ndef f := 0\n";
        assert!(check("Grass/X.lean", source, &known).is_empty());
    }

    #[test]
    fn claim_naming_an_invented_declaration_is_reported() {
        let known = known_set(&["encode"]);
        let source = "/-- `encode` ensures every address has one encoding, as proved by \
                      `encodeMem_is_canonical_and_injective`. -/\n";
        let findings = check("Grass/X.lean", source, &known);
        assert_eq!(findings.len(), 1);
        assert!(
            findings[0].contains("['encodeMem_is_canonical_and_injective']"),
            "the resolvable `encode` must not mask the invented name: {}",
            findings[0]
        );
        assert!(findings[0].starts_with("Grass/X.lean:1: claim names "));
    }

    #[test]
    fn claim_naming_nothing_is_reported() {
        let known = known_set(&["f"]);
        let findings = check(
            "Grass/X.lean",
            "/-- This ensures the flag is clear. -/",
            &known,
        );
        assert_eq!(findings.len(), 1);
        assert!(findings[0].contains("claim names no enforcing type or theorem"));
    }

    #[test]
    fn claim_naming_only_unknown_prose_is_reported_as_unresolved() {
        // `RAX` is prose, not a Lean-style declaration name, so this takes the
        // "knows no such declaration" branch rather than the "invented" one.
        let findings = check(
            "Grass/X.lean",
            "/-- The rule ensures `RAX` is untouched. -/",
            &known_set(&["f"]),
        );
        assert_eq!(findings.len(), 1);
        assert!(
            findings[0].contains("['RAX'] but the build knows no such declaration"),
            "{}",
            findings[0]
        );
    }

    #[test]
    fn a_hedged_claim_is_exempt() {
        let known = known_set(&["f"]);
        assert!(check(
            "Grass/X.lean",
            "/-- This ensures nothing yet; it is an intended invariant. -/",
            &known
        )
        .is_empty());
    }

    #[test]
    fn hedges_match_as_whole_words_only() {
        // "owed" inside `Allowed` and "M8" inside `imm8` are the substring
        // exemptions a reviewer found; neither may exempt this sentence.
        let known = known_set(&["f"]);
        let findings = check(
            "Grass/X.lean",
            "/-- The Allowed imm8 path ensures the high bits are clear. -/",
            &known,
        );
        assert_eq!(findings.len(), 1, "{findings:?}");
    }

    #[test]
    fn a_milestone_label_still_hedges() {
        let known = known_set(&["f"]);
        assert!(check(
            "Grass/X.lean",
            "/-- Nothing here ensures it; M4 owns the mechanism. -/",
            &known
        )
        .is_empty());
    }

    #[test]
    fn a_quoted_normative_passage_is_exempt() {
        let known = known_set(&["f"]);
        assert!(check(
            "Grass/X.lean",
            "/-- docs/MEMORY_IMPLEMENTATION_PLAN.md says \"the type ensures it\". -/",
            &known
        )
        .is_empty());
    }

    #[test]
    fn a_sentence_without_a_claim_word_is_ignored() {
        let known = known_set(&["f"]);
        assert!(check("Grass/X.lean", "/-- Decodes one instruction. -/", &known).is_empty());
    }

    #[test]
    fn a_dotted_suffix_of_a_known_name_resolves() {
        // `declaration_names` records every suffix, so a docstring may name
        // `writeBack.w32_clears_high` without the module prefix.
        let mut known = HashSet::new();
        known.insert("writeBack.w32_clears_high".to_string());
        assert!(check(
            "Grass/X.lean",
            "/-- The write ensures the high half is cleared, by \
             `writeBack.w32_clears_high`. -/",
            &known
        )
        .is_empty());
    }

    // --- block and sentence recognition ----------------------------------

    #[test]
    fn both_docstring_forms_are_recognised_and_ordinary_comments_are_not() {
        let source = "/-! module -/\n\n-- plain\n/- block -/\n/-- decl -/\n";
        let blocks = doc_blocks(source);
        assert_eq!(blocks, vec![(1, " module "), (5, " decl ")]);
    }

    #[test]
    fn a_block_ends_at_the_first_terminator() {
        // The Python's `(.*?)` is lazy; two blocks on one line must stay two.
        let blocks = doc_blocks("/-- a -/ /-- b -/");
        assert_eq!(blocks, vec![(1, " a "), (1, " b ")]);
    }

    #[test]
    fn sentences_split_on_full_stops_and_not_on_semicolons() {
        let split = sentences("One ensures a.\n  Two prevents b; theorem `t` proves it.");
        assert_eq!(
            split,
            vec![
                "One ensures a.".to_string(),
                "Two prevents b; theorem `t` proves it.".to_string()
            ]
        );
    }

    #[test]
    fn a_semicolon_keeps_a_claim_with_the_name_that_backs_it() {
        // Splitting on `;` would report the first clause as unbacked.
        let known = known_set(&["holds_by_construction"]);
        assert!(check(
            "Grass/X.lean",
            "/-- The step ensures progress; see `holds_by_construction`. -/",
            &known
        )
        .is_empty());
    }

    // --- file selection ---------------------------------------------------

    #[test]
    fn file_selection_takes_lean_files_at_any_depth_in_sorted_order() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path().join("Grass");
        fs::create_dir_all(root.join("ISA/X86")).expect("mkdir");
        fs::create_dir_all(root.join("Memory")).expect("mkdir");
        for relative in [
            "Zeta.lean",
            "Alpha.lean",
            "notes.md",
            "ISA/X86/Decode.lean",
            "Memory.lean",
            "Memory/State.lean",
            "Memory/State.lean.bak",
        ] {
            fs::write(root.join(relative), "").expect("write");
        }
        let found: Vec<String> = lean_files(&root, "Grass")
            .expect("walk")
            .into_iter()
            .map(|(posix, _)| posix)
            .collect();
        assert_eq!(
            found,
            vec![
                "Grass/Alpha.lean",
                "Grass/ISA/X86/Decode.lean",
                // `Memory` before `Memory.lean`: `pathlib` compares components,
                // so the directory wins over the sibling file that extends its
                // name. A flat string sort reverses this pair.
                "Grass/Memory/State.lean",
                "Grass/Memory.lean",
                "Grass/Zeta.lean",
            ]
        );
    }

    #[test]
    fn crlf_sources_are_read_as_the_python_read_them() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("X.lean");
        fs::write(&path, b"/-- a\r\nb -/\r\n").expect("write");
        assert_eq!(read_source(&path).expect("read"), "/-- a\nb -/\n");
    }

    // --- the zero-files guard --------------------------------------------

    #[test]
    fn scanning_no_files_is_a_loud_failure_not_a_clean_audit() {
        // The failure mode this port exists to close: an empty scan must not be
        // reportable as success. `run` turns an empty file list into this
        // message and exit status 1.
        let dir = tempfile::tempdir().expect("tempdir");
        let empty = dir.path().join("Grass");
        fs::create_dir_all(&empty).expect("mkdir");
        assert!(
            lean_files(&empty, "Grass").expect("walk").is_empty(),
            "the fixture must contain no .lean files for this test to mean anything"
        );

        let message = zero_files_message(&["Grass"]);
        assert!(message.contains("audited nothing"), "{message}");
        assert!(
            message.contains("Refusing to report a clean audit"),
            "{message}"
        );
        assert!(
            !message.contains("every strong claim names"),
            "an empty scan must never borrow the success line: {message}"
        );
    }

    #[test]
    fn a_missing_root_produces_no_files_rather_than_an_error() {
        // The Python skipped a missing root; that part is preserved, and it is
        // the empty file list -- not a read error -- that then fails the run.
        // This is the wrong-working-directory case exactly: `Grass` is not there.
        let dir = tempfile::tempdir().expect("tempdir");
        let missing = dir.path().join("Grass");
        assert!(!missing.is_dir());
        let files = collect_files(&[("Grass", &missing)]).expect("a missing root is not an error");
        assert!(
            files.is_empty(),
            "a missing root must yield no files, which is what `run` then refuses"
        );
    }

    // --- Python-shaped text primitives ------------------------------------

    #[test]
    fn repr_matches_python_quoting() {
        assert_eq!(py_repr("plain"), "'plain'");
        assert_eq!(py_repr("it's"), "\"it's\"");
        assert_eq!(py_repr("it's \"q\""), "'it\\'s \"q\"'");
        assert_eq!(py_repr("a\\b\nc"), "'a\\\\b\\nc'");
        assert_eq!(py_repr("em \u{2014} dash"), "'em \u{2014} dash'");
        assert_eq!(py_repr("nb\u{a0}sp"), "'nb\\xa0sp'");
    }

    #[test]
    fn list_repr_matches_python() {
        assert_eq!(py_list_repr(&[]), "[]");
        assert_eq!(py_list_repr(&["a", "b"]), "['a', 'b']");
    }

    #[test]
    fn splitlines_matches_python() {
        assert_eq!(py_splitlines("a\r\nb\nc"), vec!["a", "b", "c"]);
        assert_eq!(py_splitlines("a\n"), vec!["a"]);
        assert_eq!(py_splitlines(""), Vec::<&str>::new());
    }

    #[test]
    fn lean_style_name_is_the_shape_of_a_theorem_and_not_of_prose() {
        for name in ["encode_is_injective", "writeBack_w32", "a_b'"] {
            assert!(lean_style_name_re().is_match(name), "{name}");
        }
        for name in ["RAX", "encodeMem", "REX", "cl", "SizeOfProlog"] {
            assert!(!lean_style_name_re().is_match(name), "{name}");
        }
    }

    #[test]
    fn not_ident_cannot_fire_on_anything_ident_can_capture() {
        // Recorded rather than removed: the filter is unreachable because the
        // capture it filters admits no `/`, `§` or whitespace.
        for captured in ident_re()
            .captures_iter("`docs/x` `a b` `§` `docs` `x`")
            .map(|c| c.get(1).unwrap().as_str().to_string())
        {
            assert!(
                !not_ident_re().is_match(&captured),
                "unexpectedly reachable: {captured}"
            );
        }
    }
}
