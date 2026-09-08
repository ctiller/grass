//! Check each source document's recorded retrieval status against the network.
//!
//! `Grass.Cite.SourceDocument.livenessProbe` has existed since this corpus began
//! and had no reader. Nothing in `Tools/`, `Tests/` or `.github/` looked at it, so
//! `SourceDocument.retrieval` was a status an author typed -- and
//! `Citation.FullyChecked`, which gates `CommonBasis.agreed` and
//! `JustifiedCostModel.citationsChecked`, rested on it. Two reviewers arrived at
//! that from opposite directions: one showed a docstring claiming the status was
//! "set by probing" was simply false, and one invented a `SourceDocument` carrying
//! `.verified` and rebuilt an attack the field was added to stop.
//!
//! This is the reader. It fetches each `url` and asks whether `livenessProbe`
//! appears in what comes back, then compares that against the recorded status.
//!
//! Why a probe string rather than an HTTP status: `Grass/ISA/X86/Citation.lean`
//! records three measured ways status codes lie about exactly these two publishers.
//! `intel.com` returns 403 to an automated request while serving the manual to a
//! browser. AMD's recorded URL returns 200 with a client-routed shell identical for
//! every path on the host. And `amd.com` serves a byte-identical response for every
//! document number under both of its document trees -- so a content-length check,
//! and even a checksum-stability check, pass uniformly as well. Only asserting on
//! the document's own text separates these cases.
//!
//! What this cannot establish: that the document served is the *revision* the
//! citations were written against. The probe is a title fragment, so a publisher
//! replacing revision 092 with 093 at the same URL passes it. `Citation.confirmed`
//! still records a human following an anchor and remains unmechanised. This closes
//! the narrower question of whether the recorded retrieval status is true today.
//!
//! Exit status is 1 when a recorded status disagrees with what the network says.
//! A recorded `verified` whose probe is absent is the serious direction: the corpus
//! claims a checkable source and does not have one. A recorded `dead` whose probe
//! is present is also reported, because a document that came back is no longer a
//! release blocker and the ledger should stop saying it is.
//!
//! This needs the network, so it is not a hermetic build gate.
//! `docs/VALIDATION.md` section 7 separates scheduled campaigns from the
//! per-commit suite, and this belongs with the physical probes rather than with the
//! differentials. A network failure is reported as `unreachable` and is not
//! silently treated as a dead source: "the check could not run" and "the document
//! is gone" are different findings, and conflating them is how a corpus acquires a
//! false release blocker.
//!
//! # Why the HTTP goes through `curl`
//!
//! The Python used `urllib`. This crate is dependency-thin on purpose and has no
//! TLS stack, and both recorded URLs are `https`, so the request is delegated to
//! `curl` rather than reimplemented. That is not a weakening of the probe: the
//! Python's own header records that `intel.com` answers 403 "to `urllib` and to
//! `curl` alike, with a browser user agent and a full `Accept` header set", so the
//! two clients are already known to be interchangeable against this publisher set.
//! What matters is the three-way outcome -- served, refused, unreachable -- and
//! `curl` reports all three distinguishably: a body plus a status code on success
//! or refusal, and a non-zero exit for a transport failure.
//!
//! # One deliberate departure from the Python
//!
//! A corpus file that yields no rows is refused by name, before any decision logic
//! runs. The Python reached the same exit status through its `EXPECTED_ROWS`
//! shortfall check, but reported it as "fewer rows than reviewed against", which
//! describes a narrowed corpus rather than the thing that actually happened -- a
//! generator that produced nothing, or a path that pointed at the wrong file. An
//! audit that checked nothing must say so in those words. See `parse_rows` and
//! `empty_corpus_message`.

use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::{Command, ExitCode};

const TIMEOUT_SECONDS: u64 = 60;

/// The corpus is generated from `Vendor`, which is a closed inductive with two
/// constructors, so this is the whole of it. A row count guards against the
/// generator being narrowed the way a reviewer narrowed the NASM corpus.
const EXPECTED_ROWS: usize = 2;

/// A browser user agent, which helps with some publishers and not with these two:
/// `intel.com` answers 403 to `urllib` and to `curl` alike, with this agent and a
/// full `Accept` header set. It is presented anyway because it costs nothing and
/// a future re-pin may land on a host that honours it. What actually separates
/// bot policy from a dead document here is the refusal handling in `fetch`, not
/// this string.
const USER_AGENT: &str = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 \
                          (KHTML, like Gecko) Chrome/124.0 Safari/537.36";

/// What the Python printed from `__doc__` when invoked without exactly one
/// argument, reproduced verbatim so the usage text a human reads is unchanged.
const USAGE: &str = "Check each source document's recorded retrieval status against the network.

`Grass.Cite.SourceDocument.livenessProbe` has existed since this corpus began
and had no reader. Nothing in `Tools/`, `Tests/` or `.github/` looked at it, so
`SourceDocument.retrieval` was a status an author typed -- and
`Citation.FullyChecked`, which gates `CommonBasis.agreed` and
`JustifiedCostModel.citationsChecked`, rested on it. Two reviewers arrived at
that from opposite directions: one showed a docstring claiming the status was
\"set by probing\" was simply false, and one invented a `SourceDocument` carrying
`.verified` and rebuilt an attack the field was added to stop.

This is the reader. It fetches each `url` and asks whether `livenessProbe`
appears in what comes back, then compares that against the recorded status.

Why a probe string rather than an HTTP status: `Grass/ISA/X86/Citation.lean`
records three measured ways status codes lie about exactly these two publishers.
`intel.com` returns 403 to an automated request while serving the manual to a
browser. AMD's recorded URL returns 200 with a client-routed shell identical for
every path on the host. And `amd.com` serves a byte-identical response for every
document number under both of its document trees -- so a content-length check,
and even a checksum-stability check, pass uniformly as well. Only asserting on
the document's own text separates these cases.

What this cannot establish: that the document served is the *revision* the
citations were written against. The probe is a title fragment, so a publisher
replacing revision 092 with 093 at the same URL passes it. `Citation.confirmed`
still records a human following an anchor and remains unmechanised. This closes
the narrower question of whether the recorded retrieval status is true today.

Usage:
    lake env lean --run Tests/ISA/X86/SourceCorpus.lean > sources.txt
    source-liveness sources.txt

Exit status is 1 when a recorded status disagrees with what the network says.
A recorded `verified` whose probe is absent is the serious direction: the corpus
claims a checkable source and does not have one. A recorded `dead` whose probe
is present is also reported, because a document that came back is no longer a
release blocker and the ledger should stop saying it is.

This needs the network, so it is not a hermetic build gate.
`docs/VALIDATION.md` section 7 separates scheduled campaigns from the
per-commit suite, and this belongs with the physical probes rather than with the
differentials. A network failure is reported as `unreachable` and is not
silently treated as a dead source: \"the check could not run\" and \"the document
is gone\" are different findings, and conflating them is how a corpus acquires a
false release blocker.
";

/// One corpus row: `id<TAB>status<TAB>probe<TAB>url`, as
/// `Tests/ISA/X86/SourceCorpus.lean` prints it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    id: String,
    status: String,
    probe: String,
    url: String,
}

/// What came back from the network, in the three-way shape `fetch` documents.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Fetched {
    text: String,
    refusal: String,
    error: String,
}

/// How one row's recorded status stands against what the location served.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome {
    /// The recorded status matches, or is `unverified` and so claims nothing.
    Agreed { present: bool },
    /// The ledger says one thing and the network says another.
    Disagrees { note: String },
    /// The publisher declined to serve a robot. Never counted as death.
    Refused { refusal: String },
    /// The check could not run. Never counted as death either.
    Unreachable { error: String },
}

/// Return (text, refusal, error). At most one of the last two is non-empty.
///
/// Three outcomes, not two, because this publisher set demands it.
///
/// A `refusal` is the publisher declining to serve an automated client at all.
/// `intel.com` answers 403 with a 464-byte page to `urllib` and to `curl`
/// alike, with a browser user agent and a full `Accept` header set -- it serves
/// the manual to a real browser and not to this. That is a statement about bot
/// policy and *not* evidence about the document, which is exactly the trap
/// `Grass.Cite.RetrievalStatus` was written around: "a status checker reports a
/// live source dead". A first version of this tool fell into it and reported
/// the Intel record as disagreeing.
///
/// So a refusal is reported and never counted as death. The remediation is a
/// browser, which is how the recorded status was established in the first
/// place.
///
/// A refusal that nonetheless contains the document's title is still a live
/// document, so the body is carried back alongside the refusal and examined
/// before the status is trusted.
fn fetch(url: &str) -> Fetched {
    let scratch = match tempfile::tempdir() {
        Ok(dir) => dir,
        Err(err) => {
            return Fetched {
                error: format!("could not create a scratch directory for the response: {err}"),
                ..Fetched::default()
            }
        }
    };
    let body_path = scratch.path().join("body");

    let output = Command::new("curl")
        .arg("--silent")
        .arg("--show-error")
        // Redirects are followed, as `urllib` followed them; the recorded AMD
        // URL is a redirect to a client-routed shell.
        .arg("--location")
        .arg("--max-time")
        .arg(TIMEOUT_SECONDS.to_string())
        .arg("--user-agent")
        .arg(USER_AGENT)
        .arg("--output")
        .arg(&body_path)
        // The body goes to a file so that this, the status line, is the only
        // thing on stdout.
        .arg("--write-out")
        .arg("%{http_code}")
        .arg(url)
        .output();

    let output = match output {
        Ok(output) => output,
        Err(err) => {
            return Fetched {
                error: format!("curl could not be run: {err}"),
                ..Fetched::default()
            }
        }
    };
    if !output.status.success() {
        // A transport failure: DNS, TLS, timeout, connection refused. This is
        // the `unreachable` case, and deliberately not the `dead` one.
        let detail = String::from_utf8_lossy(&output.stderr);
        let detail = detail.trim();
        let code = output
            .status
            .code()
            .map_or_else(|| "signal".to_string(), |code| code.to_string());
        return Fetched {
            error: if detail.is_empty() {
                format!("curl exit {code}")
            } else {
                format!("curl exit {code}: {detail}")
            },
            ..Fetched::default()
        };
    }

    // `errors="replace"` in the Python decoded undecodable bytes to U+FFFD;
    // lossy decoding substitutes the same character.
    let text = fs::read(&body_path)
        .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
        .unwrap_or_default();
    let status_code = String::from_utf8_lossy(&output.stdout)
        .trim()
        .parse::<u32>()
        .unwrap_or(0);

    // `urllib` raised `HTTPError` for a final status of 400 or above, which is
    // the branch that produced a refusal; everything else was a served body.
    if status_code >= 400 {
        // Character count, not byte count, because the Python measured the
        // decoded string. The word in the message stays "bytes" so the text a
        // human compares against the previous tool is unchanged.
        let size = text.chars().count();
        return Fetched {
            text,
            refusal: format!("HTTP {status_code} ({size} bytes)"),
            error: String::new(),
        };
    }
    Fetched {
        text,
        refusal: String::new(),
        error: String::new(),
    }
}

/// Decide what one row's fetch means for the status the corpus recorded.
///
/// Split out from the reporting so the decision can be tested without a
/// network: every branch below is reachable from a `Fetched` built by hand.
fn classify(row: &Row, fetched: &Fetched) -> Outcome {
    if !fetched.error.is_empty() {
        return Outcome::Unreachable {
            error: fetched.error.clone(),
        };
    }
    let present = fetched.text.contains(&row.probe);
    if !fetched.refusal.is_empty() && !present {
        // The publisher declined to serve a robot. That says nothing about
        // whether the document is there; see `fetch`.
        return Outcome::Refused {
            refusal: fetched.refusal.clone(),
        };
    }
    if row.status == "verified" && !present {
        return Outcome::Disagrees {
            note: format!(
                "recorded verified, but {} is absent from {} bytes served",
                py_repr(&row.probe),
                fetched.text.chars().count()
            ),
        };
    }
    if row.status == "dead" && present {
        return Outcome::Disagrees {
            note: format!(
                "recorded dead, but {} is present in what the location serves; it may have come \
                 back",
                py_repr(&row.probe)
            ),
        };
    }
    Outcome::Agreed { present }
}

/// Parse the tab-separated corpus the Lean generator prints.
///
/// Blank lines are skipped and a trailing carriage return is tolerated, which is
/// what `line.rstrip("\r")` did for a corpus captured on Windows. A row with any
/// field count other than four is a malformed corpus, not a row to guess at.
fn parse_rows(text: &str) -> Result<Vec<Row>, String> {
    let mut rows = Vec::new();
    for line in py_splitlines(text) {
        if py_strip(line).is_empty() {
            continue;
        }
        let fields: Vec<&str> = line.trim_end_matches('\r').split('\t').collect();
        if fields.len() != 4 {
            return Err(format!("malformed corpus row: {}", py_repr(line)));
        }
        rows.push(Row {
            id: fields[0].to_string(),
            status: fields[1].to_string(),
            probe: fields[2].to_string(),
            url: fields[3].to_string(),
        });
    }
    Ok(rows)
}

/// The message behind this port's one deliberate departure from the Python.
///
/// A corpus that parsed to nothing checks nothing, and the Python described that
/// as a shortfall against `EXPECTED_ROWS` -- true, but it points at the corpus
/// having been narrowed rather than at the generator or the path being wrong,
/// which is what actually produces an empty file.
fn empty_corpus_message(path: &str) -> String {
    format!(
        "source liveness: {path} contained no corpus rows, so nothing was checked.\n\
         Refusing to report a clean probe against an empty corpus: regenerate it with\n\
         `lake env lean --run Tests/ISA/X86/SourceCorpus.lean > {path}`."
    )
}

/// The Python's `EXPECTED_ROWS` shortfall message, unchanged.
fn short_corpus_message(rows: usize) -> String {
    format!(
        "corpus has {rows} rows, fewer than the {EXPECTED_ROWS} this tool was reviewed against. \
         Coverage may only grow; if the reduction is deliberate, lower EXPECTED_ROWS in the same \
         reviewed edit that shrinks the corpus."
    )
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 1 {
        println!("{USAGE}");
        return ExitCode::from(2);
    }
    match run(&args[0]) {
        Ok(code) => code,
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

fn run(corpus_path: &str) -> Result<ExitCode, String> {
    let bytes = fs::read(Path::new(corpus_path))
        .map_err(|err| format!("could not read the corpus {corpus_path}: {err}"))?;
    let text = String::from_utf8(bytes)
        .map_err(|err| format!("corpus {corpus_path} is not valid UTF-8: {err}"))?;
    let rows = parse_rows(&normalise_newlines(&text))?;

    if rows.is_empty() {
        return Err(empty_corpus_message(corpus_path));
    }
    if rows.len() < EXPECTED_ROWS {
        return Err(short_corpus_message(rows.len()));
    }

    let mut disagreements = Vec::new();
    let mut unreachable = Vec::new();
    let mut refused = Vec::new();
    let mut agreed = Vec::new();
    for row in &rows {
        match classify(row, &fetch(&row.url)) {
            Outcome::Unreachable { error } => unreachable.push((row, error)),
            Outcome::Refused { refusal } => refused.push((row, refusal)),
            Outcome::Disagrees { note } => disagreements.push((row, note)),
            Outcome::Agreed { present } => agreed.push((row, present)),
        }
    }

    for (row, note) in &disagreements {
        eprintln!("DISAGREES  {}", row.id);
        eprintln!("    url    {}", row.url);
        eprintln!("    {note}");
    }
    for (row, error) in &unreachable {
        eprintln!("UNREACHABLE  {}: {error}", row.id);
        eprintln!("    url  {}", row.url);
        eprintln!(
            "    Not counted as dead: a check that could not run and a document that is gone are \
             different findings."
        );
    }
    for (row, refusal) in &refused {
        println!("REFUSED  {}: {refusal}, recorded {}", row.id, row.status);
        println!("    url  {}", row.url);
        println!(
            "    The publisher declined to serve an automated client. This is bot policy, not \
             evidence about the document, and is not counted as death -- confirm in a browser."
        );
    }

    if !disagreements.is_empty() {
        eprintln!(
            "source liveness: {} documents, {} disagree with their recorded status, {} unreachable",
            rows.len(),
            disagreements.len(),
            unreachable.len()
        );
        return Ok(ExitCode::FAILURE);
    }

    let summary = if agreed.is_empty() {
        "none checkable".to_string()
    } else {
        agreed
            .iter()
            .map(|(row, present)| {
                format!(
                    "{} {} (probe {})",
                    row.id,
                    row.status,
                    if *present { "found" } else { "absent" }
                )
            })
            .collect::<Vec<_>>()
            .join(", ")
    };
    let mut extra = String::new();
    if !refused.is_empty() {
        let _ = write!(extra, "; {} refused an automated client", refused.len());
    }
    if !unreachable.is_empty() {
        let _ = write!(extra, "; {} unreachable", unreachable.len());
    }
    println!(
        "source liveness: {} documents, {} confirmed against what the location serves -- \
         {summary}{extra}",
        rows.len(),
        agreed.len()
    );
    Ok(ExitCode::SUCCESS)
}

// ---------------------------------------------------------------------------
// Python-shaped text primitives.
//
// Duplicated from `docstring_audit.rs` rather than shared: each tool in this
// crate is invoked independently and a change to one must not be able to alter
// another's verdict, which is why `Cargo.toml` declares binaries and no library.
// ---------------------------------------------------------------------------

/// `Path.read_text` opened in text mode, so `\r\n` and a lone `\r` both reached
/// the parser as `\n`.
fn normalise_newlines(text: &str) -> String {
    if !text.contains('\r') {
        return text.to_string();
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
    out
}

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

/// Python's `repr()` for a `str`, which is how a probe string and a malformed
/// row are quoted in the messages a reviewer compares run to run.
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

/// Python's `str.isprintable()`, to the precision this corpus needs.
///
/// Python calls a character unprintable when its category is `Cc`, `Cf`, `Cs`,
/// `Co`, `Cn`, `Zl`, `Zp` or `Zs` -- except U+0020, which is printable. Rust's
/// standard library exposes no category table, so the separators and format
/// controls that can plausibly reach a probe string are listed and everything
/// else non-ASCII is treated as printable.
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

    fn row(status: &str) -> Row {
        Row {
            id: "intel-325383".to_string(),
            status: status.to_string(),
            probe: "Software Developer".to_string(),
            url: "https://example.invalid/doc".to_string(),
        }
    }

    fn served(body: &str) -> Fetched {
        Fetched {
            text: body.to_string(),
            ..Fetched::default()
        }
    }

    // --- the rule that decides a violation -------------------------------

    #[test]
    fn a_verified_record_whose_probe_is_absent_disagrees() {
        // The serious direction: the corpus claims a checkable source and does
        // not have one.
        let outcome = classify(&row("verified"), &served("<html>not the manual</html>"));
        match outcome {
            Outcome::Disagrees { note } => {
                assert!(note.starts_with("recorded verified, but 'Software Developer' is absent"));
                assert!(note.ends_with("from 27 bytes served"), "{note}");
            }
            other => panic!("expected a disagreement, got {other:?}"),
        }
    }

    #[test]
    fn a_verified_record_whose_probe_is_present_agrees() {
        assert_eq!(
            classify(
                &row("verified"),
                &served("Intel 64 Software Developer's Manual")
            ),
            Outcome::Agreed { present: true }
        );
    }

    #[test]
    fn a_dead_record_whose_probe_is_present_disagrees() {
        // A document that came back is no longer a release blocker.
        match classify(&row("dead"), &served("... Software Developer ...")) {
            Outcome::Disagrees { note } => {
                assert!(note.contains("it may have come back"), "{note}")
            }
            other => panic!("expected a disagreement, got {other:?}"),
        }
    }

    #[test]
    fn a_dead_record_whose_probe_is_absent_agrees() {
        assert_eq!(
            classify(&row("dead"), &served("404")),
            Outcome::Agreed { present: false }
        );
    }

    #[test]
    fn an_unverified_record_never_disagrees() {
        // `unverified` claims nothing, so neither answer can contradict it.
        for body in ["Software Developer", "gone"] {
            assert!(matches!(
                classify(&row("unverified"), &served(body)),
                Outcome::Agreed { .. }
            ));
        }
    }

    // --- the two outcomes that must never be read as death ----------------

    #[test]
    fn a_refusal_is_reported_and_not_counted_as_death() {
        // `Grass.Cite.RetrievalStatus` was written around exactly this trap:
        // "a status checker reports a live source dead".
        let fetched = Fetched {
            text: "Access Denied".to_string(),
            refusal: "HTTP 403 (464 bytes)".to_string(),
            error: String::new(),
        };
        assert_eq!(
            classify(&row("verified"), &fetched),
            Outcome::Refused {
                refusal: "HTTP 403 (464 bytes)".to_string()
            }
        );
    }

    #[test]
    fn a_refusal_that_still_carries_the_document_is_a_live_document() {
        // The body is examined before the status code is trusted.
        let fetched = Fetched {
            text: "403, and yet: Software Developer".to_string(),
            refusal: "HTTP 403 (32 bytes)".to_string(),
            error: String::new(),
        };
        assert_eq!(
            classify(&row("verified"), &fetched),
            Outcome::Agreed { present: true }
        );
    }

    #[test]
    fn a_transport_failure_is_unreachable_and_not_a_disagreement() {
        let fetched = Fetched {
            error: "curl exit 6: Could not resolve host".to_string(),
            ..Fetched::default()
        };
        match classify(&row("verified"), &fetched) {
            Outcome::Unreachable { error } => assert!(error.contains("Could not resolve host")),
            other => panic!("a check that could not run is not a dead document: {other:?}"),
        }
    }

    // --- corpus selection and parsing -------------------------------------

    #[test]
    fn rows_parse_on_tabs_and_blank_lines_are_skipped() {
        let text = "a\tverified\tprobe one\thttps://x/1\n\n  \nb\tdead\tprobe two\thttps://x/2\n";
        let rows = parse_rows(text).expect("parse");
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].probe, "probe one");
        assert_eq!(rows[1].url, "https://x/2");
    }

    #[test]
    fn a_windows_captured_corpus_parses() {
        let rows = parse_rows(&normalise_newlines(
            "a\tverified\tp\thttps://x/1\r\nb\tdead\tq\thttps://x/2\r\n",
        ))
        .expect("parse");
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[1].url, "https://x/2");
    }

    #[test]
    fn a_row_with_the_wrong_field_count_is_refused() {
        let err = parse_rows("a\tverified\thttps://x/1\n").expect_err("must be refused");
        assert_eq!(
            err, "malformed corpus row: 'a\\tverified\\thttps://x/1'",
            "the offending line is quoted the way the Python quoted it"
        );
    }

    // --- the empty-corpus guard -------------------------------------------

    #[test]
    fn an_empty_corpus_checks_nothing_and_says_so() {
        // The failure mode this port exists to close: probing nothing must not
        // be reportable as a clean probe.
        for text in ["", "\n\n   \n"] {
            assert!(
                parse_rows(text)
                    .expect("blank input is not malformed")
                    .is_empty(),
                "blank input must yield no rows for this test to mean anything"
            );
        }
        let message = empty_corpus_message("sources.txt");
        assert!(message.contains("contained no corpus rows"), "{message}");
        assert!(
            message.contains("Refusing to report a clean probe"),
            "{message}"
        );
        assert!(
            !message.contains("confirmed against what the location serves"),
            "an empty corpus must never borrow the success line: {message}"
        );
    }

    #[test]
    fn a_missing_corpus_file_is_a_named_failure_not_a_panic() {
        let dir = tempfile::tempdir().expect("tempdir");
        let missing = dir.path().join("sources.txt");
        let err = run(&missing.to_string_lossy()).expect_err("must fail");
        assert!(err.starts_with("could not read the corpus "), "{err}");
    }

    #[test]
    fn a_short_corpus_keeps_the_pythons_wording() {
        let message = short_corpus_message(1);
        assert!(message.starts_with("corpus has 1 rows, fewer than the 2 this tool was reviewed"));
        assert!(message.contains("lower EXPECTED_ROWS"));
    }

    // --- Python-shaped text primitives ------------------------------------

    #[test]
    fn repr_matches_python_quoting() {
        assert_eq!(py_repr("plain"), "'plain'");
        assert_eq!(py_repr("it's"), "\"it's\"");
        assert_eq!(py_repr("a\tb"), "'a\\tb'");
        assert_eq!(py_repr("nb\u{a0}sp"), "'nb\\xa0sp'");
    }

    #[test]
    fn splitlines_matches_python() {
        assert_eq!(py_splitlines("a\r\nb\nc"), vec!["a", "b", "c"]);
        assert_eq!(py_splitlines(""), Vec::<&str>::new());
    }
}
