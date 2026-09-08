//! Differential check of Grass's RIP-relative encoding against NDISASM.
//!
//! `docs/VALIDATION.md` section 2 layer 2 asks for comparison against independent
//! decoders and disassemblers. This is the disassembler half; the assembler half is
//! `x86-nasm-differential`.
//!
//! It exists because the RIP-relative form is the one an assembler cannot check.
//! NASM computes a RIP displacement from a target address and an instruction
//! length, so a source line asserting a literal displacement tests NASM's
//! arithmetic rather than Grass's encoding. A disassembler has the opposite
//! property: given bytes, NDISASM prints the absolute target it computed, and that
//! number is exactly what the RIP contract is about.
//!
//! Which matters, because `mod=00, rm=101` is the form whose meaning is unique to
//! 64-bit mode -- in 32-bit mode the same encoding is an absolute displacement --
//! and it is the form behind every import call and the payload address in Spike 1.
//! Without this check it had no external validation at all.
//!
//! ## What the target number tests
//!
//! The displacement is relative to the address of the *next* instruction. So
//! disassembled at origin 0, an instruction of length n with displacement d must
//! print target n + d. That single number separates three distinct mistakes:
//!
//!   * resolving against the start of the instruction instead of the end;
//!   * resolving against the end of the displacement field rather than the end of
//!     the instruction -- which differ only when a trailing immediate is present,
//!     so the `mov` rows carrying an imm32 are the ones that tell those apart;
//!   * a reversed displacement byte order, which moves the target far.
//!
//! NDISASM is a fallible oracle, not authority. `docs/VALIDATION.md` section 2:
//! "Disagreement is preserved as a finding; majority vote does not establish
//! truth."
//!
//! Usage:
//!     lake env lean --run Tests/ISA/X86/RipCorpus.lean > rip.txt
//!     x86-ndisasm-differential rip.txt
//!
//! Exit status is 1 on any mismatch.

use std::path::{Path, PathBuf};
use std::process::Command;

use regex::Regex;

/// Operand-size and distance keywords NDISASM prints and Grass does not model as
/// text. Stripping them, along with spaces and case, leaves the part that is a
/// fact about the encoding: the mnemonic, the register, and the target.
///
/// The order is load-bearing: "dword" has to go before "word", or the inner
/// substring is removed first and leaves a stray "d" behind.
const NOISE: [&str; 7] = ["qword", "dword", "word", "byte", "near", "short", "far"];

/// The corpus this tool was last reviewed against. See `corpus_digest`.
const EXPECTED_DIGEST: &str = "bdda43a6e9d2850aafcccadda4c6f4b756af6f9972f326623dbebc37ecdf09ee";

/// The coverage this tool was reviewed at. Shrinking the corpus must be a
/// deliberate, reviewed edit rather than a side effect of regenerating it.
///
/// The digest above detects a substituted corpus but not a smaller one: an author
/// who shrinks the generator gets a digest mismatch, is told to update the
/// constant, updates it, and the tool passes over the smaller corpus. A reviewer
/// demonstrated it -- one `.take 1` plus a digest update turned 1085 encodings
/// into 1 and still reported no disagreement. `docs/VALIDATION.md` section 7's
/// ratchet is meant to prevent exactly that, and this is it applied to corpora.
const EXPECTED_ROWS: usize = 19;

/// One corpus row: the bytes Grass emitted, the absolute target Grass predicts
/// NDISASM will print, the normalised operand text it predicts, and a label.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    bytes: Vec<u8>,
    target: i128,
    expected_text: String,
    label: String,
}

/// A row NDISASM did not confirm, with the sentence explaining how.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Finding {
    label: String,
    hexed: String,
    detail: String,
}

// ---------------------------------------------------------------------------
// Corpus coverage digest
// ---------------------------------------------------------------------------

/// The row's label and expected disassembly. The first column is the bytes
/// Grass emitted.
fn coverage_of(line: &str) -> String {
    let fields: Vec<&str> = line.split('\t').collect();
    if fields.len() > 2 {
        fields[2..].join("\t")
    } else {
        line.to_string()
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
///
/// Note that the target column is *not* covered here, so a corpus whose
/// predicted targets were edited reaches NDISASM rather than the guard. That is
/// deliberate for the same reason: the target is a claim about the encoding, and
/// claims are for the oracle to settle.
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

/// Split the corpus into rows of exactly four columns.
///
/// A short row is fatal rather than skipped: the columns are a prediction, and a
/// row whose prediction this tool cannot read is a row it would stop checking
/// while still counting towards `EXPECTED_ROWS`.
fn parse_corpus(text: &str) -> Result<Vec<Row>, String> {
    let mut rows = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.splitn(4, '\t').collect();
        if parts.len() != 4 {
            return Err(format!(
                "malformed corpus line, expected 4 fields: {}",
                py_repr(line)
            ));
        }
        let bytes = from_hex(parts[0])
            .ok_or_else(|| format!("corpus line has non-hex bytes: {}", py_repr(line)))?;
        let target = py_int_base16(parts[1])
            .ok_or_else(|| format!("corpus line has an unreadable target: {}", py_repr(line)))?;
        rows.push(Row {
            bytes,
            target,
            expected_text: parts[2].to_string(),
            label: parts[3].to_string(),
        });
    }
    Ok(rows)
}

// ---------------------------------------------------------------------------
// NDISASM
// ---------------------------------------------------------------------------

fn find_tool(name: &str) -> PathBuf {
    if let Some(found) = which(name) {
        return found;
    }
    for candidate in [
        home_dir().map(|h| h.join(format!("AppData/Local/bin/NASM/{name}.exe"))),
        Some(PathBuf::from(format!("C:/Program Files/NASM/{name}.exe"))),
    ]
    .into_iter()
    .flatten()
    {
        if candidate.exists() {
            return candidate;
        }
    }
    die(&format!(
        "{name} not found on PATH or in the usual install locations"
    ));
}

/// NDISASM starts each instruction with its 8-hex-digit address in column 0, and
/// wraps an instruction whose bytes do not fit onto continuation lines that are
/// indented and begin with "-". Counting raw lines therefore reports a long
/// instruction as several, which is how this tool first reported the two `mov`
/// rows -- the only rows long enough to wrap -- as length errors when their
/// targets were in fact correct.
fn instruction_line_re() -> Regex {
    Regex::new(r"^[0-9A-F]{8}\s").expect("static regex")
}

/// NDISASM prints "00000000  4C8D2D44332211    lea r13,[rel 0x11223351]".
fn target_re() -> Regex {
    Regex::new(r"\[rel (0x[0-9a-fA-F]+)\]").expect("static regex")
}

/// Split NDISASM's stdout into the text it printed and the count of instructions
/// it found.
///
/// The count matters: if Grass's bytes decode as more than one instruction,
/// the length is wrong even when the first line looks right.
fn summarise(stdout: &str) -> (String, usize) {
    let re = instruction_line_re();
    let lines: Vec<&str> = stdout
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect();
    let starts = lines.iter().filter(|line| re.is_match(line)).count();
    (lines.join("\n"), starts)
}

/// Disassemble one instruction at origin 0; return its text and the count of
/// instructions NDISASM found, or `None` if NDISASM refused the bytes.
fn disassemble(ndisasm: &Path, raw: &[u8]) -> Option<(String, usize)> {
    let tmp = match tempfile::tempdir() {
        Ok(tmp) => tmp,
        Err(e) => die(&format!("could not create a temporary directory: {e}")),
    };
    let binary = tmp.path().join("insn.bin");
    if let Err(e) = std::fs::write(&binary, raw) {
        die(&format!("could not write {}: {e}", binary.display()));
    }
    let result = match Command::new(ndisasm)
        .args(["-b", "64"])
        .arg(&binary)
        .output()
    {
        Ok(result) => result,
        Err(e) => die(&format!("could not run {}: {e}", ndisasm.display())),
    };
    if !result.status.success() {
        return None;
    }
    Some(summarise(&String::from_utf8_lossy(&result.stdout)))
}

// ---------------------------------------------------------------------------
// Comparison
// ---------------------------------------------------------------------------

/// The comparable part of a disassembly line.
///
/// The target alone is not enough. Both Grass's expected target and NDISASM's
/// are functions of the same instruction length, so they move together: a
/// reviewer stripped REX.W from all sixteen `lea` rows -- turning
/// `lea rax,[rel ...]` into the different instruction `lea eax,[rel ...]` --
/// and every row still agreed. Replacing all nineteen rows with identical bytes
/// also passed. The register field was invisible until this compared text.
fn normalise(text: &str) -> String {
    // The address and byte columns are dropped by taking everything after the
    // first two whitespace-separated fields, exactly as Python's
    // `str.split(None, 2)` did.
    let mut rest = text.trim_start();
    let mut body = "";
    for step in 0..2 {
        match rest.find(char::is_whitespace) {
            Some(cut) => {
                rest = rest[cut..].trim_start();
                if step == 1 {
                    body = rest;
                }
            }
            None => {
                body = "";
                break;
            }
        }
    }
    let mut lowered = body.to_lowercase();
    for word in NOISE {
        lowered = lowered.replace(word, "");
    }
    lowered.split_whitespace().collect()
}

/// Judge one row against what NDISASM said, returning the sentence that explains
/// the disagreement or `None` when the two agree.
///
/// Pure so that every branch can be exercised without NDISASM on the machine
/// running the tests; the process boundary is `disassemble`'s only job.
fn evaluate(row: &Row, disassembly: Option<&(String, usize)>) -> Option<String> {
    let Some((text, count)) = disassembly else {
        return Some("ndisasm refused the bytes".to_string());
    };
    if *count != 1 {
        return Some(format!(
            "decoded as {count} instructions, so the length is wrong:\n{text}"
        ));
    }
    let Some(found) = target_re().captures(text) else {
        return Some(format!(
            "no RIP-relative target in the disassembly: {}",
            text.trim()
        ));
    };
    let actual = py_int_base16(&found[1]).expect("regex matched 0x-prefixed hex");
    if actual != row.target {
        return Some(format!(
            "target {}, expected {} (instruction length {}); {}",
            py_hex(actual),
            py_hex(row.target),
            row.bytes.len(),
            text.trim()
        ));
    }
    let got = normalise(text);
    if !got.starts_with(&row.expected_text) {
        return Some(format!(
            "operands {} do not start with the predicted {}",
            py_repr(&got),
            py_repr(&row.expected_text)
        ));
    }
    None
}

/// The human-readable verdict and the exit status that goes with it.
fn report(rows: usize, mismatches: &[Finding]) -> (String, i32) {
    let mut out = format!(
        "x86 NDISASM differential: {rows} RIP-relative encodings, {} agree\n",
        rows - mismatches.len()
    );
    if !mismatches.is_empty() {
        out.push_str(&format!("\n{} mismatch(es):\n\n", mismatches.len()));
        // Only the first 40 are printed. Unlike the NASM differential there is no
        // "... and N more" line; with a 19-row corpus the cap is unreachable, and
        // the omission is preserved rather than quietly corrected so that the two
        // tools' outputs stay the ones their reviews were written against.
        for finding in mismatches.iter().take(40) {
            out.push_str(&format!("  {}\n", finding.label));
            out.push_str(&format!("    grass: {}\n", finding.hexed));
            out.push_str(&format!("    {}\n", finding.detail));
        }
        return (out, 1);
    }
    out.push_str("no disagreement\n");
    (out, 0)
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
        // The Python original named itself `x86-ndisasm-differential.py` here.
        // That is the one place this port does not reproduce its text: a message
        // telling the reader to run a file that is no longer the tool sends them
        // looking for the wrong thing.
        die("usage: x86-ndisasm-differential <rip.txt>");
    }
    let ndisasm = find_tool("ndisasm");

    let path = Path::new(&args[0]);
    let text = match read_text(path) {
        Ok(text) => text,
        Err(e) => die(&format!("{}: {e}", path.display())),
    };
    let rows = match parse_corpus(&text) {
        Ok(rows) => rows,
        Err(e) => die(&e),
    };

    if rows.is_empty() {
        die("corpus is empty; did the Lean generator run?");
    }
    if rows.len() < EXPECTED_ROWS {
        die(&format!(
            "corpus has {} rows, fewer than the {EXPECTED_ROWS} this tool was \
             reviewed against. Coverage may only grow; if the reduction is \
             deliberate, lower EXPECTED_ROWS in the same reviewed edit that \
             shrinks the corpus.",
            rows.len()
        ));
    }

    let actual_digest = corpus_digest(&text);
    if actual_digest != EXPECTED_DIGEST {
        die(&format!(
            "corpus digest {actual_digest} does not match the reviewed \
             {EXPECTED_DIGEST}. Regenerate it from the Lean corpus, or update \
             EXPECTED_DIGEST here if the corpus genuinely changed."
        ));
    }

    let mut mismatches = Vec::new();
    for row in &rows {
        // One NDISASM invocation per row. The corpus is nineteen rows, and each
        // must be disassembled at origin 0 for its printed target to mean what
        // the check is about.
        let disassembly = disassemble(&ndisasm, &row.bytes);
        if let Some(detail) = evaluate(row, disassembly.as_ref()) {
            mismatches.push(Finding {
                label: row.label.clone(),
                hexed: hex_of(&row.bytes),
                detail,
            });
        }
    }

    let (text, code) = report(rows.len(), &mismatches);
    print!("{text}");
    code
}

// ---------------------------------------------------------------------------
// Shared helpers
//
// Deliberately duplicated across the three differentials rather than factored
// into a library: each is invoked independently by CI, and a change to one must
// not be able to move another's verdict.
// ---------------------------------------------------------------------------

/// Report a fatal problem the way the Python `sys.exit("...")` did: the message
/// on stderr, status 1.
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
    // `as_chunks` rather than `chunks_exact`: the odd-length guard above means
    // the remainder is empty, and a `&[u8; 2]` indexes without a bounds check.
    let (pairs, _) = digits.as_chunks::<2>();
    pairs
        .iter()
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

/// Python's `int(text, 16)`: surrounding whitespace, an optional sign, an
/// optional `0x` prefix and `_` separators are all accepted.
fn py_int_base16(text: &str) -> Option<i128> {
    let text = text.trim();
    let (negative, rest) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text.strip_prefix('+').unwrap_or(text)),
    };
    let rest = rest
        .strip_prefix("0x")
        .or_else(|| rest.strip_prefix("0X"))
        .unwrap_or(rest);
    let digits: String = rest.chars().filter(|c| *c != '_').collect();
    if digits.is_empty() {
        return None;
    }
    let value = i128::from_str_radix(&digits, 16).ok()?;
    Some(if negative { -value } else { value })
}

/// Python's `f"{value:#x}"`, which writes a negative number as `-0x..` rather
/// than as a two's-complement pattern the way Rust's `{:#x}` would.
fn py_hex(value: i128) -> String {
    if value < 0 {
        format!("-0x{:x}", value.unsigned_abs())
    } else {
        format!("0x{value:x}")
    }
}

/// Python's `repr` of a string, used for the mismatch details and the
/// malformed-line message. Reproduced so that a disagreement reported by this
/// tool reads the same as one reported by the script it replaced, including
/// which whitespace character was in the way.
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

    // The padding loop above makes `msg` a whole number of 64-byte blocks, so
    // both remainders here are empty. `as_chunks` yields `&[u8; N]`, which
    // `from_be_bytes` takes directly.
    let (blocks, _) = msg.as_chunks::<64>();
    for block in blocks {
        let mut w = [0u32; 64];
        let (words, _) = block.as_chunks::<4>();
        for (i, word) in words.iter().enumerate() {
            w[i] = u32::from_be_bytes(*word);
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

    /// The first row of the real corpus, which is what every assertion about the
    /// happy path here is calibrated against.
    fn lea_rax() -> Row {
        Row {
            bytes: from_hex("488d0544332211").unwrap(),
            target: 0x1122334b,
            expected_text: "learax,[rel0x1122334b]".to_string(),
            label: "lea rax, [rip+disp]".to_string(),
        }
    }

    fn lea_rax_disassembly() -> (String, usize) {
        (
            "00000000  488D0544332211    lea rax,[rel 0x1122334b]".to_string(),
            1,
        )
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
    fn parses_four_column_rows() {
        let rows =
            parse_corpus("488d0544332211\t1122334b\tlearax,[rel0x1122334b]\tlea rax, [rip+disp]\n")
                .unwrap();
        assert_eq!(rows, vec![lea_rax()]);
    }

    #[test]
    fn blank_and_whitespace_only_lines_are_skipped() {
        let text = "\n90\t1\ta\tb\n   \n90\t1\ta\tb\n";
        assert_eq!(parse_corpus(text).unwrap().len(), 2);
    }

    #[test]
    fn a_short_row_is_fatal() {
        let err = parse_corpus("90\t1\tonly three\n").unwrap_err();
        assert!(err.contains("expected 4 fields"), "{err}");
        assert!(err.contains("'90\\t1\\tonly three'"), "{err}");
    }

    #[test]
    fn a_fifth_tab_belongs_to_the_label() {
        // The label is free text and may contain tabs; only the first three
        // separators are structural.
        let rows = parse_corpus("90\t1\ta\tlabel\twith tab\n").unwrap();
        assert_eq!(rows[0].label, "label\twith tab");
    }

    #[test]
    fn the_target_column_accepts_a_bare_or_prefixed_hex_number() {
        assert_eq!(
            parse_corpus("90\t1122334b\ta\tb\n").unwrap()[0].target,
            0x1122334b
        );
        assert_eq!(parse_corpus("90\t0x1f\ta\tb\n").unwrap()[0].target, 0x1f);
        assert!(parse_corpus("90\tzz\ta\tb\n")
            .unwrap_err()
            .contains("target"));
    }

    #[test]
    fn digest_ignores_the_byte_and_target_columns() {
        // The bytes and the predicted target are claims under test; only the
        // label and expected disassembly describe what is covered.
        let before = corpus_digest("488d05\t1122334b\tlearax,[rel0x1122334b]\tlea\n");
        let after = corpus_digest("0000\tdeadbeef\tlearax,[rel0x1122334b]\tlea\n");
        assert_eq!(before, after);
    }

    #[test]
    fn digest_notices_dropped_and_reordered_rows() {
        let full = corpus_digest("90\t1\ta\tone\n90\t1\tb\ttwo\n");
        assert_ne!(full, corpus_digest("90\t1\ta\tone\n"));
        assert_ne!(full, corpus_digest("90\t1\tb\ttwo\n90\t1\ta\tone\n"));
    }

    #[test]
    fn digest_is_independent_of_line_endings() {
        assert_eq!(
            corpus_digest("90\t1\ta\tone\n"),
            corpus_digest("90\t1\ta\tone\r\n")
        );
    }

    #[test]
    fn coverage_of_a_column_less_line_is_the_whole_line() {
        assert_eq!(coverage_of("no tabs"), "no tabs");
        assert_eq!(coverage_of("one\ttwo"), "one\ttwo");
    }

    #[test]
    fn normalise_drops_the_address_and_byte_columns_and_the_size_keywords() {
        assert_eq!(
            normalise("00000000  488D0544332211    lea rax,[rel 0x1122334b]"),
            "learax,[rel0x1122334b]"
        );
        assert_eq!(
            normalise("00000000  48C70544332211AA  mov qword [rel 0x1122334f],0xaa"),
            "mov[rel0x1122334f],0xaa"
        );
    }

    #[test]
    fn normalise_strips_dword_before_word() {
        // "word" is a substring of "dword"; removing it first would leave a "d".
        assert_eq!(normalise("00 00 dword [rel 0x1]"), "[rel0x1]");
    }

    #[test]
    fn normalise_of_a_line_with_fewer_than_three_fields_is_empty() {
        assert_eq!(normalise("00000000  90"), "");
        assert_eq!(normalise(""), "");
    }

    #[test]
    fn an_agreeing_row_produces_no_finding() {
        assert_eq!(evaluate(&lea_rax(), Some(&lea_rax_disassembly())), None);
    }

    #[test]
    fn a_refusal_is_a_finding() {
        assert_eq!(
            evaluate(&lea_rax(), None),
            Some("ndisasm refused the bytes".to_string())
        );
    }

    #[test]
    fn bytes_that_decode_as_two_instructions_are_a_length_error() {
        let detail = evaluate(&lea_rax(), Some(&("00000000  90  nop".to_string(), 2))).unwrap();
        assert!(detail.starts_with("decoded as 2 instructions, so the length is wrong:\n"));
    }

    #[test]
    fn a_disassembly_without_a_rip_target_is_a_finding() {
        let disasm = ("00000000  90                nop".to_string(), 1);
        let detail = evaluate(&lea_rax(), Some(&disasm)).unwrap();
        assert_eq!(
            detail,
            "no RIP-relative target in the disassembly: 00000000  90                nop"
        );
    }

    #[test]
    fn a_wrong_target_reports_both_numbers_and_the_length() {
        let disasm = (
            "00000000  488D0544332211    lea rax,[rel 0x11223344]".to_string(),
            1,
        );
        let detail = evaluate(&lea_rax(), Some(&disasm)).unwrap();
        assert!(
            detail.starts_with("target 0x11223344, expected 0x1122334b (instruction length 7); "),
            "{detail}"
        );
    }

    #[test]
    fn a_right_target_with_the_wrong_register_is_still_a_finding() {
        // The mutation that motivated comparing text: dropping REX.W turns this
        // into `lea eax`, and the target is unchanged because the length is.
        let disasm = (
            "00000000  8D0544332211      lea eax,[rel 0x1122334b]".to_string(),
            1,
        );
        let mut row = lea_rax();
        row.target = 0x1122334b;
        let detail = evaluate(&row, Some(&disasm)).unwrap();
        assert!(
            detail.contains("do not start with the predicted"),
            "{detail}"
        );
        assert!(detail.contains("'leaeax,[rel0x1122334b]'"), "{detail}");
    }

    #[test]
    fn a_trailing_operand_beyond_the_prediction_is_accepted() {
        // The prediction is a prefix check, so a row may predict less than the
        // whole operand text; only a divergence at the front is a finding.
        let mut row = lea_rax();
        row.expected_text = "learax,".to_string();
        assert_eq!(evaluate(&row, Some(&lea_rax_disassembly())), None);
    }

    #[test]
    fn a_clean_run_exits_zero() {
        let (text, code) = report(19, &[]);
        assert_eq!(code, 0);
        assert_eq!(
            text,
            "x86 NDISASM differential: 19 RIP-relative encodings, 19 agree\nno disagreement\n"
        );
    }

    #[test]
    fn any_mismatch_exits_one() {
        let mismatches = vec![Finding {
            label: "lea rax, [rip+disp]".to_string(),
            hexed: "488d0544332211".to_string(),
            detail: "ndisasm refused the bytes".to_string(),
        }];
        let (text, code) = report(19, &mismatches);
        assert_eq!(code, 1);
        assert!(text.starts_with("x86 NDISASM differential: 19 RIP-relative encodings, 18 agree\n"));
        assert!(text.contains(
            "\n1 mismatch(es):\n\n  lea rax, [rip+disp]\n    grass: 488d0544332211\n    ndisasm refused the bytes\n"
        ));
        assert!(!text.contains("no disagreement"));
    }

    #[test]
    fn py_repr_quotes_the_way_python_did() {
        assert_eq!(py_repr("plain"), "'plain'");
        assert_eq!(py_repr("a\tb"), "'a\\tb'");
        assert_eq!(py_repr("it's"), "\"it's\"");
        assert_eq!(py_repr("back\\slash"), "'back\\\\slash'");
    }

    #[test]
    fn py_hex_writes_a_negative_with_a_leading_minus() {
        assert_eq!(py_hex(0x1f), "0x1f");
        assert_eq!(py_hex(0), "0x0");
        assert_eq!(py_hex(-0x1f), "-0x1f");
    }

    #[test]
    fn summarise_counts_instruction_starts_not_lines() {
        // A wrapped encoding continues on an indented line with no address, and
        // counting raw lines reported those rows as length errors.
        let stdout = "00000000  48B8887766554433  mov rax,0x1122334455667788\n\
                      \x20         -2211\n";
        let (text, count) = summarise(stdout);
        assert_eq!(count, 1);
        assert_eq!(text.lines().count(), 2);
    }

    #[test]
    fn from_hex_matches_python_fromhex() {
        assert_eq!(from_hex("48 8d"), Some(vec![0x48, 0x8d]));
        assert_eq!(from_hex(""), Some(vec![]));
        assert_eq!(from_hex("4"), None);
        assert_eq!(from_hex("4g"), None);
    }
}
