//! Differential check of the Grass x86-64 decoder's instruction lengths against NDISASM.
//!
//! `docs/VALIDATION.md` section 2 layer 2 asks for comparison against independent
//! tools. The two existing x86 differentials check the *encoder*: they take bytes
//! Grass emitted and ask NASM or NDISASM whether they mean what Grass says. Nothing
//! checked the decoder, and an adversarial reviewer showed precisely what that
//! omission was worth -- five separate mutations survived `lake build` and both of
//! those tools:
//!
//! * `0x83`'s immediate widened from `imm8` to `imm32`
//! * `0x8D` marked as taking no ModR/M byte
//! * `0xC7`'s immediate removed
//! * `dispKindFor`'s `mod=01` branch changed from `disp8` to none
//! * `dispKindFor`'s `mod=00`-with-SIB branch changed from none to `disp32`
//!
//! None of them is subtle; each corrupts thousands of real instruction lengths. The
//! reason they survived is structural. `MatchesSpec` requires an `InsnEncoding` and
//! its `OpcodeSpec` row to agree with *each other*, never with the ISA, so the
//! opcode table carries no evidence at all. And `dispKindFor` is the single
//! definition behind both `InsnEncoding.WellFormed` and `decodeOperands`, so
//! changing it moves encoder and decoder together and the round-trip theorem still
//! closes. The encoder differentials could not reach the two `dispKindFor` branches
//! either, because `encodeMem` never emits `mod=01` and never emits a `mod=00` SIB
//! with a base other than `101`.
//!
//! The same gap hid a real bug rather than only hypothetical ones: `B8+rd` under
//! `REX.W` is `mov r64, imm64`, and the decoder read four immediate bytes where
//! eight follow, then resumed four bytes inside the immediate.
//!
//! Length is what this compares, and length alone. It is the property a wrong table
//! or a wrong displacement rule destroys; it is the property that turns one bad
//! instruction into a corrupt instruction stream; and it is the one NDISASM reports
//! unambiguously, as the offset where the next instruction starts.
//!
//! Usage:
//!     lake env lean --run Tests/ISA/X86/DecodeCorpus.lean > decode.txt
//!     x86-decode-differential decode.txt
//!
//! Exit status is 1 on any length disagreement, and on a missing NDISASM: a
//! differential that passes because its oracle is absent is worse than none.
//!
//! NDISASM is a fallible oracle, not authority. `docs/VALIDATION.md` section 2:
//! "Tools and hardware are fallible oracles. Disagreement is preserved as a
//! finding; majority vote does not establish truth."
//!
//! `DOC` below repeats this text verbatim because the Python original answered a
//! wrong argument count by printing its own `__doc__` and exiting 2 -- the
//! rationale doubles as the usage message. A Rust doc comment cannot be read at
//! run time, so the printed copy is a constant, and the two are kept in step by
//! hand. The only line that differs from the Python `__doc__` is the invocation
//! under "Usage": a message telling the reader to run
//! `python Tools/x86-decode-differential.py` sends them looking for a file that
//! is no longer the tool.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use regex::Regex;

/// The module documentation above, verbatim, for the usage path to print.
const DOC: &str = r#"Differential check of the Grass x86-64 decoder's instruction lengths against NDISASM.

`docs/VALIDATION.md` section 2 layer 2 asks for comparison against independent
tools. The two existing x86 differentials check the *encoder*: they take bytes
Grass emitted and ask NASM or NDISASM whether they mean what Grass says. Nothing
checked the decoder, and an adversarial reviewer showed precisely what that
omission was worth -- five separate mutations survived `lake build` and both of
those tools:

* `0x83`'s immediate widened from `imm8` to `imm32`
* `0x8D` marked as taking no ModR/M byte
* `0xC7`'s immediate removed
* `dispKindFor`'s `mod=01` branch changed from `disp8` to none
* `dispKindFor`'s `mod=00`-with-SIB branch changed from none to `disp32`

None of them is subtle; each corrupts thousands of real instruction lengths. The
reason they survived is structural. `MatchesSpec` requires an `InsnEncoding` and
its `OpcodeSpec` row to agree with *each other*, never with the ISA, so the
opcode table carries no evidence at all. And `dispKindFor` is the single
definition behind both `InsnEncoding.WellFormed` and `decodeOperands`, so
changing it moves encoder and decoder together and the round-trip theorem still
closes. The encoder differentials could not reach the two `dispKindFor` branches
either, because `encodeMem` never emits `mod=01` and never emits a `mod=00` SIB
with a base other than `101`.

The same gap hid a real bug rather than only hypothetical ones: `B8+rd` under
`REX.W` is `mov r64, imm64`, and the decoder read four immediate bytes where
eight follow, then resumed four bytes inside the immediate.

Length is what this compares, and length alone. It is the property a wrong table
or a wrong displacement rule destroys; it is the property that turns one bad
instruction into a corrupt instruction stream; and it is the one NDISASM reports
unambiguously, as the offset where the next instruction starts.

Usage:
    lake env lean --run Tests/ISA/X86/DecodeCorpus.lean > decode.txt
    x86-decode-differential decode.txt

Exit status is 1 on any length disagreement, and on a missing NDISASM: a
differential that passes because its oracle is absent is worse than none.

NDISASM is a fallible oracle, not authority. `docs/VALIDATION.md` section 2:
"Tools and hardware are fallible oracles. Disagreement is preserved as a
finding; majority vote does not establish truth."
"#;

/// The corpus this tool was reviewed against, as a digest of its content. A row
/// count is not enough: a truncated or duplicated corpus keeps a plausible count
/// and checks nothing. See the same guard in the other x86 differentials.
const EXPECTED_DIGEST: &str = "9ac7a927b227758adeabb508806d7d1bc291e715ce635478bc7cb5d929177c75";

/// The coverage this tool was reviewed at. Shrinking the corpus must be a
/// deliberate, reviewed edit rather than a side effect of regenerating it.
///
/// The digest above detects a substituted corpus but not a smaller one: an author
/// who shrinks the generator gets a digest mismatch, is told to update the
/// constant, updates it, and the tool passes over the smaller corpus. A reviewer
/// demonstrated it -- one `.take 1` plus a digest update turned 1085 encodings
/// into 1 and still reported no disagreement. `docs/VALIDATION.md` section 7's
/// ratchet is meant to prevent exactly that, and this is it applied to corpora.
const EXPECTED_ROWS: usize = 57440;

/// Must match `Grass.Tests.ISA.X86.DecodeC.windowBytes`. The tool checks this
/// against the corpus rather than trusting it.
const WINDOW_BYTES: usize = 24;

/// One corpus row: the fixed-width window Grass built, the length Grass's decoder
/// reported for the instruction at its start, and the label naming what is covered.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    window: Vec<u8>,
    grass_len: usize,
    label: String,
}

/// A window where Grass and NDISASM chose different instruction boundaries.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Disagreement {
    label: String,
    hexbytes: String,
    grass: usize,
    oracle: usize,
    asm: String,
}

/// What a pass over the whole corpus concluded.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Outcome {
    disagreements: Vec<Disagreement>,
    /// Windows NDISASM would not read as an instruction at all. Counted, not
    /// compared: this decoder accepts encodings NDISASM rejects, by design.
    refused: usize,
    /// Windows NDISASM's boundaries walked into or over, so no comparison at the
    /// window's own start was possible. A failure, not a skip -- an overrun is
    /// precisely the corruption this tool exists to catch.
    unaligned: usize,
}

// ---------------------------------------------------------------------------
// Corpus coverage digest
// ---------------------------------------------------------------------------

/// The window's label, which names the opcode row, prefix and operand bytes. The
/// other columns are the window Grass built and the length it reported -- both
/// under test.
fn coverage_of(line: &str) -> &str {
    match line.split('\t').nth(2) {
        Some(field) => field,
        None => line,
    }
}

/// A digest of the corpus's *coverage*, line endings normalised.
///
/// Hashes the columns that say what is exercised and not the columns holding
/// what Grass emitted. That distinction was missing and it mattered: a reviewer
/// mutated `encodeMem`, and this tool's entire output was the digest error
/// telling them to update the constant. Following it, the real check reported
/// 60 mismatches -- so the guard fired first on precisely the change it adds
/// nothing to, and its own remedy was to silence it. That is the shape of the
/// row-count weakness described beside `EXPECTED_ROWS`, one column over.
///
/// Hashing coverage keeps what the guard is for. A corpus that drops rows,
/// duplicates them, or swaps hard cases for easy ones still changes this
/// digest; a corpus whose byte column changed because the encoder changed does
/// not, and goes straight to the oracle that can judge it.
fn corpus_digest(text: &str) -> String {
    let normalised = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| coverage_of(line.trim_end_matches('\r')))
        .collect::<Vec<_>>()
        .join("\n");
    sha256_hex(normalised.as_bytes())
}

// ---------------------------------------------------------------------------
// Corpus parsing
// ---------------------------------------------------------------------------

/// Split the corpus into rows of exactly three columns, each carrying a full
/// window.
///
/// The window width is checked here rather than assumed: the offsets this tool
/// compares are computed as `index * WINDOW_BYTES` into one concatenated blob, so
/// a corpus built with a different width would silently compare the wrong bytes.
fn parse_corpus(text: &str) -> Result<Vec<Row>, String> {
    let mut rows = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let fields: Vec<&str> = line.trim_end_matches('\r').split('\t').collect();
        if fields.len() != 3 {
            return Err(format!("malformed corpus row: {}", py_repr(line)));
        }
        let window = from_hex(fields[0])
            .ok_or_else(|| format!("malformed corpus row: {}", py_repr(line)))?;
        if window.len() != WINDOW_BYTES {
            return Err(format!(
                "row {} is {} bytes, expected {WINDOW_BYTES}; the corpus and this \
                 tool disagree about the window size",
                fields[2],
                window.len()
            ));
        }
        let grass_len = py_int_base10(fields[1])
            .ok_or_else(|| format!("malformed corpus row: {}", py_repr(line)))?;
        rows.push(Row {
            window,
            grass_len,
            label: fields[2].to_string(),
        });
    }
    Ok(rows)
}

// ---------------------------------------------------------------------------
// NDISASM
// ---------------------------------------------------------------------------

fn find_tool(name: &str) -> Option<PathBuf> {
    if let Some(found) = which(name) {
        return Some(found);
    }
    [
        home_dir().map(|h| h.join(format!("AppData/Local/bin/NASM/{name}.exe"))),
        Some(PathBuf::from(format!("C:/Program Files/NASM/{name}.exe"))),
    ]
    .into_iter()
    .flatten()
    .find(|candidate| candidate.exists())
}

fn line_re() -> Regex {
    Regex::new(r"^([0-9A-Fa-f]{8})\s+([0-9A-Fa-f]+)\s+(\S.*)$").expect("static regex")
}

/// NDISASM's two ways of saying "these bytes are not an instruction".
///
/// `db 0x..` is the obvious one. The other is subtler and accounts for three
/// quarters of the cases here: given a REX prefix followed by bytes that do not
/// form a legal instruction, NDISASM emits the prefix on a line of its own and
/// resumes after it. `48 8D C0` -- LEA with `mod=11`, which is #UD because LEA
/// has no register-source form -- prints as `rex.w` and then `db 0x8d`. Reading
/// that first line as an instruction boundary would report a length of 1 and
/// call it a disagreement, when what NDISASM actually said is that it refused.
fn prefix_only_re() -> Regex {
    // Anchored end-to-end because the Python used `fullmatch`; the `^`/`$` inside
    // the original alternation were redundant under it.
    Regex::new(r"(?i)\A(?:rex(\.[wrxb]+)?|o16|o32|a16|a32)\z").expect("static regex")
}

/// Whether NDISASM declined to read an instruction at this offset.
fn is_refusal(text: &str) -> bool {
    text.starts_with("db ") || prefix_only_re().is_match(text)
}

/// Read NDISASM's stdout into the text at each instruction start.
///
/// Continuation lines for long encodings carry no address and are dropped, which
/// is what makes the surviving keys exactly the boundaries NDISASM chose.
fn parse_disassembly(stdout: &str) -> HashMap<usize, String> {
    let re = line_re();
    let mut text_at = HashMap::new();
    for line in stdout.lines() {
        let Some(caps) = re.captures(line) else {
            continue;
        };
        let Ok(address) = usize::from_str_radix(&caps[1], 16) else {
            continue;
        };
        text_at.insert(address, caps[3].trim().to_string());
    }
    text_at
}

/// Disassemble the whole corpus in one pass.
///
/// One invocation rather than one per row: 57k separate processes would take
/// hours, and NDISASM decodes a flat blob continuously, which is exactly what
/// is wanted here -- the boundaries it chooses *are* the lengths being checked.
fn disassemble_blob(ndisasm: &Path, blob: &[u8]) -> HashMap<usize, String> {
    let tmp = match tempfile::tempdir() {
        Ok(tmp) => tmp,
        Err(e) => die(&format!("could not create a temporary directory: {e}")),
    };
    let binary = tmp.path().join("corpus.bin");
    if let Err(e) = std::fs::write(&binary, blob) {
        die(&format!("could not write {}: {e}", binary.display()));
    }
    let proc = match Command::new(ndisasm)
        .args(["-b", "64"])
        .arg(&binary)
        .output()
    {
        Ok(proc) => proc,
        Err(e) => die(&format!("could not run {}: {e}", ndisasm.display())),
    };
    if !proc.status.success() {
        let stderr = String::from_utf8_lossy(&proc.stderr);
        let trimmed = stderr.trim();
        let clipped: String = trimmed.chars().take(300).collect();
        die(&format!("ndisasm failed: {clipped}"));
    }
    parse_disassembly(&String::from_utf8_lossy(&proc.stdout))
}

// ---------------------------------------------------------------------------
// Comparison
// ---------------------------------------------------------------------------

/// Compare Grass's length for each window against the boundary NDISASM chose.
///
/// Pure in the disassembly so every branch -- agreement, refusal, overrun, and
/// disagreement -- is reachable in tests without NDISASM installed.
fn compare(rows: &[Row], text_at: &HashMap<usize, String>) -> Outcome {
    let start_set: HashSet<usize> = text_at.keys().copied().collect();
    let mut outcome = Outcome::default();
    for (index, row) in rows.iter().enumerate() {
        let base = index * WINDOW_BYTES;
        if !start_set.contains(&base) {
            // NDISASM's boundaries drifted into this window, which means the
            // previous instruction overran it. Reported rather than skipped.
            outcome.unaligned += 1;
            continue;
        }
        let asm = &text_at[&base];
        if is_refusal(asm) {
            outcome.refused += 1;
            continue;
        }
        let Some(next) = (1..=WINDOW_BYTES).find(|k| start_set.contains(&(base + k))) else {
            outcome.unaligned += 1;
            continue;
        };
        if next != row.grass_len {
            let shown = next.max(row.grass_len).min(row.window.len());
            outcome.disagreements.push(Disagreement {
                label: row.label.clone(),
                hexbytes: hex_of(&row.window[..shown]),
                grass: row.grass_len,
                oracle: next,
                asm: asm.clone(),
            });
        }
    }
    outcome
}

/// The human-readable verdict and the exit status that goes with it, as
/// (stdout, stderr, status).
///
/// Everything about a failing run goes to stderr, including the summary, so that
/// a CI log shows the disagreements and the count they came from together.
fn report(rows: usize, outcome: &Outcome) -> (String, String, i32) {
    let mut err = String::new();
    for d in outcome.disagreements.iter().take(40) {
        err.push_str(&format!("LENGTH  {}\n", d.label));
        err.push_str(&format!("    bytes    {}\n", d.hexbytes));
        err.push_str(&format!("    grass    {}\n", d.grass));
        err.push_str(&format!("    ndisasm  {}  ({})\n", d.oracle, d.asm));
    }
    if outcome.disagreements.len() > 40 {
        err.push_str(&format!(
            "    ... and {} more\n",
            outcome.disagreements.len() - 40
        ));
    }

    let checked = rows - outcome.refused - outcome.unaligned;
    if !outcome.disagreements.is_empty() || outcome.unaligned > 0 {
        err.push_str(&format!(
            "x86 decode differential: {rows} windows, {checked} compared, {} length \
             disagreements, {} refused by ndisasm as invalid encodings, {} unaligned\n",
            outcome.disagreements.len(),
            outcome.refused,
            outcome.unaligned
        ));
        return (String::new(), err, 1);
    }

    let out = format!(
        "x86 decode differential: {rows} windows, {checked} compared, lengths agree \
         with ndisasm on all of them; {} further windows are encodings ndisasm \
         rejects as invalid, which this decoder accepts by design and which are not \
         compared\n",
        outcome.refused
    );
    (out, err, 0)
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn main() {
    std::process::exit(run());
}

fn run() -> i32 {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 1 {
        // Status 2, not 1: a usage error is not a finding about the decoder, and
        // CI must not read it as one.
        println!("{DOC}");
        return 2;
    }

    let path = Path::new(&args[0]);
    let text = match read_text(path) {
        Ok(text) => text,
        Err(e) => {
            eprintln!("{}: {e}", path.display());
            return 1;
        }
    };

    // The digest is checked before the rows are parsed, so a corpus from a
    // different generator is named as such rather than as a row-shaped error.
    let actual = corpus_digest(&text);
    if actual != EXPECTED_DIGEST {
        eprintln!(
            "corpus digest {actual} does not match the reviewed {EXPECTED_DIGEST}. \
             Regenerate it from the Lean corpus, or update EXPECTED_DIGEST here if \
             the corpus genuinely changed."
        );
        return 1;
    }

    let rows = match parse_corpus(&text) {
        Ok(rows) => rows,
        Err(e) => {
            eprintln!("{e}");
            return 1;
        }
    };
    if rows.is_empty() {
        eprintln!("corpus is empty");
        return 1;
    }
    if rows.len() < EXPECTED_ROWS {
        eprintln!(
            "corpus has {} rows, fewer than the {EXPECTED_ROWS} this tool was \
             reviewed against. Coverage may only grow; if the reduction is \
             deliberate, lower EXPECTED_ROWS in the same reviewed edit that shrinks \
             the corpus.",
            rows.len()
        );
        return 1;
    }

    let Some(ndisasm) = find_tool("ndisasm") else {
        eprintln!(
            "ndisasm not found on PATH or in the usual install locations. This is a \
             failure rather than a skip: a differential check that passes because \
             its oracle is absent is worse than no check."
        );
        return 1;
    };

    let blob: Vec<u8> = rows.iter().flat_map(|r| r.window.iter().copied()).collect();
    let text_at = disassemble_blob(&ndisasm, &blob);

    let outcome = compare(&rows, &text_at);
    let (out, err, code) = report(rows.len(), &outcome);
    print!("{out}");
    eprint!("{err}");
    code
}

// ---------------------------------------------------------------------------
// Shared helpers
//
// Deliberately duplicated across the three differentials rather than factored
// into a library: each is invoked independently by CI, and a change to one must
// not be able to move another's verdict.
// ---------------------------------------------------------------------------

/// Report a fatal problem the way the Python `raise SystemExit("...")` did: the
/// message on stderr, status 1.
fn die(message: &str) -> ! {
    eprintln!("{message}");
    std::process::exit(1);
}

/// Read a file the way Python's text mode did, collapsing CRLF and lone CR to
/// LF. The corpus is generated on Windows in one CI job and Linux in another,
/// and the coverage digest must not depend on which.
fn read_text(path: &Path) -> Result<String, String> {
    let raw = std::fs::read(path).map_err(|e| e.to_string())?;
    let text = String::from_utf8(raw).map_err(|e| e.to_string())?;
    Ok(text.replace("\r\n", "\n").replace('\r', "\n"))
}

/// Decode a hex string, ignoring embedded ASCII whitespace as Python's
/// `bytes.fromhex` does. `None` for an odd digit count or a non-hex character.
fn from_hex(text: &str) -> Option<Vec<u8>> {
    let digits: Vec<u8> = text.bytes().filter(|b| !b.is_ascii_whitespace()).collect();
    if !digits.len().is_multiple_of(2) {
        return None;
    }
    digits
        .chunks_exact(2)
        .map(|pair| {
            let hi = (pair[0] as char).to_digit(16)?;
            let lo = (pair[1] as char).to_digit(16)?;
            Some((hi * 16 + lo) as u8)
        })
        .collect()
}

fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Python's `int(text)`: surrounding whitespace, an optional sign and `_`
/// separators are accepted. A negative length is rejected here rather than
/// wrapping, since it can only be a corrupt corpus.
fn py_int_base10(text: &str) -> Option<usize> {
    let text = text.trim();
    let rest = text.strip_prefix('+').unwrap_or(text);
    let digits: String = rest.chars().filter(|c| *c != '_').collect();
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

/// Python's `repr` of a string, for the malformed-row message. Reproduced so
/// that a corpus bug reported by this tool reads the same as one reported by the
/// script it replaced, including which whitespace character was in the way.
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
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                out.push_str(&format!("\\x{:02x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push(quote);
    out
}

fn home_dir() -> Option<PathBuf> {
    // `Path.home()` resolves to USERPROFILE on Windows and HOME elsewhere; both
    // are consulted so the same binary finds NDISASM on a developer's machine
    // and in the Linux CI job.
    std::env::var_os("USERPROFILE")
        .or_else(|| std::env::var_os("HOME"))
        .map(PathBuf::from)
}

/// A `shutil.which` equivalent, including its Windows behaviour of searching the
/// current directory and appending each PATHEXT suffix.
fn which(name: &str) -> Option<PathBuf> {
    let exts: Vec<String> = match std::env::var("PATHEXT") {
        Ok(pathext) if !pathext.is_empty() => std::iter::once(String::new())
            .chain(
                pathext
                    .split(';')
                    .filter(|e| !e.is_empty())
                    .map(str::to_string),
            )
            .collect(),
        _ => vec![String::new()],
    };
    let mut dirs: Vec<PathBuf> = Vec::new();
    if cfg!(windows) {
        dirs.push(PathBuf::from("."));
    }
    if let Some(path) = std::env::var_os("PATH") {
        dirs.extend(std::env::split_paths(&path));
    }
    for dir in dirs {
        for ext in &exts {
            let candidate = dir.join(format!("{name}{ext}"));
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// SHA-256
//
// Written out rather than pulled in as a dependency: the digest is a guard
// against a substituted corpus, and a guard whose implementation arrives from
// outside the repository is a weaker guard than one that does not.
// ---------------------------------------------------------------------------

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

fn sha256_hex(data: &[u8]) -> String {
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut msg = data.to_vec();
    let bit_len = (data.len() as u64).wrapping_mul(8);
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());

    for block in msg.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, word) in block.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
            (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
        for (k, wi) in SHA256_K.iter().zip(w.iter()) {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(*k)
                .wrapping_add(*wi);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (slot, value) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *slot = slot.wrapping_add(value);
        }
    }
    h.iter().map(|word| format!("{word:08x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A 24-byte window whose first `len` bytes are the instruction under test.
    fn window(hex: &str) -> String {
        let mut w = hex.to_string();
        while w.len() < WINDOW_BYTES * 2 {
            w.push_str("90");
        }
        w
    }

    fn row(hex: &str, grass_len: usize, label: &str) -> Row {
        Row {
            window: from_hex(&window(hex)).unwrap(),
            grass_len,
            label: label.to_string(),
        }
    }

    #[test]
    fn sha256_matches_published_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        // Long enough to need a second block, which is where a padding bug hides.
        assert_eq!(
            sha256_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    #[test]
    fn parses_three_column_rows() {
        let text = format!("{}\t7\t8D /r lea\n", window("488d8044332211"));
        let rows = parse_corpus(&text).unwrap();
        assert_eq!(rows, vec![row("488d8044332211", 7, "8D /r lea")]);
    }

    #[test]
    fn blank_lines_are_skipped() {
        let w = window("90");
        let text = format!("\n{w}\t1\ta\n  \n{w}\t1\tb\n");
        assert_eq!(parse_corpus(&text).unwrap().len(), 2);
    }

    #[test]
    fn a_row_with_the_wrong_column_count_is_rejected() {
        let w = window("90");
        assert!(parse_corpus(&format!("{w}\t1\n"))
            .unwrap_err()
            .contains("malformed corpus row"));
        assert!(parse_corpus(&format!("{w}\t1\ta\tb\n"))
            .unwrap_err()
            .contains("malformed corpus row"));
    }

    #[test]
    fn a_short_window_names_the_row_and_the_expected_width() {
        let err = parse_corpus("90\t1\t8D /r lea\n").unwrap_err();
        assert_eq!(
            err,
            "row 8D /r lea is 1 bytes, expected 24; the corpus and this tool \
             disagree about the window size"
        );
    }

    #[test]
    fn a_non_numeric_length_is_rejected() {
        let w = window("90");
        assert!(parse_corpus(&format!("{w}\tseven\ta\n"))
            .unwrap_err()
            .contains("malformed corpus row"));
    }

    #[test]
    fn digest_ignores_the_window_and_length_columns() {
        // Both are claims under test; only the label says what is covered.
        let a = corpus_digest("aabb\t2\t8D /r lea\n");
        let b = corpus_digest("ccdd\t9\t8D /r lea\n");
        assert_eq!(a, b);
    }

    #[test]
    fn digest_notices_dropped_and_reordered_rows() {
        let full = corpus_digest("aa\t1\tone\nbb\t1\ttwo\n");
        assert_ne!(full, corpus_digest("aa\t1\tone\n"));
        assert_ne!(full, corpus_digest("bb\t1\ttwo\naa\t1\tone\n"));
        assert_ne!(full, corpus_digest("aa\t1\tone\nbb\t1\ttwo\naa\t1\tone\n"));
    }

    #[test]
    fn digest_is_independent_of_line_endings() {
        assert_eq!(
            corpus_digest("aa\t1\tone\n"),
            corpus_digest("aa\t1\tone\r\n")
        );
    }

    #[test]
    fn refusals_are_recognised_in_both_of_ndisasms_forms() {
        assert!(is_refusal("db 0x8d"));
        assert!(is_refusal("rex.w"));
        assert!(is_refusal("rex"));
        assert!(is_refusal("REX.WRXB"));
        assert!(is_refusal("o16"));
        assert!(is_refusal("a32"));
    }

    #[test]
    fn a_real_instruction_is_not_a_refusal() {
        // Anchoring matters: `rex` as a prefix of a longer text is an
        // instruction NDISASM read, not a refusal.
        assert!(!is_refusal("lea rax,[rax+0x11223344]"));
        assert!(!is_refusal("rex.w mov rax,rcx"));
        assert!(!is_refusal("dbg something"));
        assert!(!is_refusal("o16x"));
    }

    #[test]
    fn instruction_lines_are_keyed_by_address_and_continuations_dropped() {
        let stdout = "00000000  488D8044332211    lea rax,[rax+0x11223344]\n\
                      00000018  48B8887766554433  mov rax,0x1122334455667788\n\
                      \x20         -2211\n";
        let text_at = parse_disassembly(stdout);
        assert_eq!(text_at.len(), 2);
        assert_eq!(text_at[&0], "lea rax,[rax+0x11223344]");
        assert_eq!(text_at[&0x18], "mov rax,0x1122334455667788");
    }

    /// Boundaries for a corpus of `n` windows where every instruction is `len`
    /// bytes long and the rest of each window is single-byte NOPs.
    fn boundaries(n: usize, len: usize) -> HashMap<usize, String> {
        let mut text_at = HashMap::new();
        for index in 0..n {
            let base = index * WINDOW_BYTES;
            text_at.insert(base, "lea rax,[rax+0x11223344]".to_string());
            for offset in base + len..base + WINDOW_BYTES {
                text_at.insert(offset, "nop".to_string());
            }
        }
        text_at
    }

    #[test]
    fn agreeing_lengths_produce_no_disagreement() {
        let rows = vec![row("488d8044332211", 7, "8D /r lea")];
        let outcome = compare(&rows, &boundaries(1, 7));
        assert_eq!(outcome, Outcome::default());

        let (out, err, code) = report(rows.len(), &outcome);
        assert_eq!(code, 0);
        assert!(err.is_empty());
        assert!(out.starts_with("x86 decode differential: 1 windows, 1 compared, lengths agree"));
    }

    #[test]
    fn a_wrong_length_is_reported_with_both_numbers() {
        // The `0xC7`-immediate-removed mutation has exactly this shape: Grass
        // stops early and NDISASM's next boundary is further on.
        let rows = vec![row("488d8044332211", 3, "8D /r lea")];
        let outcome = compare(&rows, &boundaries(1, 7));
        assert_eq!(outcome.disagreements.len(), 1);
        assert_eq!(outcome.disagreements[0].grass, 3);
        assert_eq!(outcome.disagreements[0].oracle, 7);
        // The bytes shown cover the longer of the two claims, so a reader can see
        // what the extra bytes were.
        assert_eq!(outcome.disagreements[0].hexbytes, "488d8044332211");

        let (out, err, code) = report(rows.len(), &outcome);
        assert_eq!(code, 1);
        assert!(out.is_empty(), "a failing run says nothing on stdout");
        assert!(err.contains("LENGTH  8D /r lea\n"));
        assert!(err.contains("    grass    3\n"));
        assert!(err.contains("    ndisasm  7  (lea rax,[rax+0x11223344])\n"));
        assert!(err.contains("1 length disagreements, 0 refused"));
    }

    #[test]
    fn a_refused_window_is_counted_and_not_compared() {
        // NDISASM rejects encodings this decoder accepts by design, so a refusal
        // must not become a length finding in either direction.
        let rows = vec![row("488dc0", 3, "8D /r lea mod=11")];
        let mut text_at = boundaries(1, 3);
        text_at.insert(0, "rex.w".to_string());
        let outcome = compare(&rows, &text_at);
        assert_eq!(outcome.refused, 1);
        assert!(outcome.disagreements.is_empty());

        let (out, _, code) = report(rows.len(), &outcome);
        assert_eq!(code, 0);
        assert!(out.contains("0 compared"));
        assert!(out.contains("1 further windows are encodings ndisasm rejects"));
    }

    #[test]
    fn an_overrun_window_is_unaligned_and_fails_the_run() {
        // If the previous instruction swallowed this window's first byte there is
        // no boundary at its base, and the corpus can no longer be trusted to line
        // up -- which is the corruption the tool exists to catch.
        let rows = vec![row("90", 1, "one"), row("90", 1, "two")];
        let mut text_at = boundaries(2, 1);
        text_at.remove(&WINDOW_BYTES);
        let outcome = compare(&rows, &text_at);
        assert_eq!(outcome.unaligned, 1);
        assert!(outcome.disagreements.is_empty());

        let (_, err, code) = report(rows.len(), &outcome);
        assert_eq!(
            code, 1,
            "an unaligned window fails even with no disagreement"
        );
        assert!(err.contains("2 windows, 1 compared, 0 length disagreements"));
        assert!(err.contains("1 unaligned"));
    }

    #[test]
    fn a_window_with_no_following_boundary_is_unaligned() {
        // NDISASM read one instruction covering the whole window and then ran out
        // of bytes, so there is no offset to measure against.
        let rows = vec![row("90", 1, "one")];
        let text_at = HashMap::from([(0usize, "lea rax,[rax+0x11223344]".to_string())]);
        let outcome = compare(&rows, &text_at);
        assert_eq!(outcome.unaligned, 1);
    }

    #[test]
    fn long_disagreement_lists_are_truncated_with_a_count() {
        let rows: Vec<Row> = (0..45).map(|i| row("90", 2, &format!("row{i}"))).collect();
        let outcome = compare(&rows, &boundaries(45, 1));
        assert_eq!(outcome.disagreements.len(), 45);
        let (_, err, code) = report(rows.len(), &outcome);
        assert_eq!(code, 1);
        assert!(err.contains("LENGTH  row39\n"));
        assert!(!err.contains("LENGTH  row40\n"));
        assert!(err.contains("    ... and 5 more\n"));
    }

    #[test]
    fn the_printed_doc_still_carries_its_rationale() {
        // The usage path prints this, so a truncation here would quietly turn the
        // explanation of what the tool is for into a bare error.
        assert!(DOC.starts_with("Differential check of the Grass x86-64 decoder's"));
        assert!(DOC.contains("dispKindFor"));
        assert!(DOC.contains("majority vote does not establish truth."));
        assert!(DOC.contains(
            "    x86-decode-differential decode.txt
"
        ));
        assert!(DOC.ends_with("truth.\"\n"));
    }

    #[test]
    fn py_repr_quotes_the_way_python_did() {
        assert_eq!(py_repr("plain"), "'plain'");
        assert_eq!(py_repr("a\tb"), "'a\\tb'");
        assert_eq!(py_repr("it's"), "\"it's\"");
        assert_eq!(py_repr("back\\slash"), "'back\\\\slash'");
    }

    #[test]
    fn from_hex_matches_python_fromhex() {
        assert_eq!(from_hex("48 8d"), Some(vec![0x48, 0x8d]));
        assert_eq!(from_hex(""), Some(vec![]));
        assert_eq!(from_hex("4"), None);
        assert_eq!(from_hex("4g"), None);
    }
}
