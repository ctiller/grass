//! Differential check of the Grass x86-64 encoder against NASM.
//!
//! `docs/VALIDATION.md` section 2 layer 2 asks for a comparison against independent
//! encoders and assemblers "where independent tools exist". NASM is one.
//!
//! This matters more than it sounds. Every theorem in `Grass/ISA/X86/**` relates
//! Grass's own definitions to each other: the round-trip theorems prove that the
//! decoder recovers what the encoder wrote, which a model with two ModR/M fields
//! transposed satisfies perfectly while emitting instructions no processor will
//! execute. An external assembler is the only thing in the repository that can
//! notice.
//!
//! NASM is a fallible oracle, not authority. `docs/VALIDATION.md` section 2:
//! "Tools and hardware are fallible oracles. Disagreement is preserved as a
//! finding; majority vote does not establish truth." A mismatch is a finding
//! against Grass *or* against NASM, and is resolved by reading the vendor manual.
//!
//! Usage:
//!     lake env lean --run Tests/ISA/X86/NasmCorpus.lean > corpus.txt
//!     x86-nasm-differential corpus.txt
//!
//! Exit status is 1 on any mismatch.
//!
//! Why the corpus uses a displacement of 0x11223344: Grass's encoder always emits a
//! 32-bit displacement, while NASM emits the shortest form. For a displacement that
//! does not fit in a signed byte the two agree exactly and a byte comparison is
//! meaningful. With a small displacement NASM would legitimately choose disp8 and
//! the comparison would report a policy difference as a defect. That restriction is
//! a real limit on what this check covers, and it is stated rather than hidden: the
//! short-displacement forms are exercised by the decoder, not by this tool.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use regex::Regex;

/// The two lines NASM needs before the corpus for the sources to mean what the
/// Lean generator meant. `DEFAULT ABS` matters: without it NASM would read a
/// bracketed absolute address as RIP-relative, which is a different encoding.
const PROLOGUE: [&str; 2] = ["BITS 64", "DEFAULT ABS"];

/// The corpus this tool was last reviewed against. See `corpus_digest`.
const EXPECTED_DIGEST: &str = "6cb8fbdf038d027991aff78e4c61ddf1a1e8bf067edfd00d505a45cb5e28a660";

/// The coverage this tool was reviewed at. Shrinking the corpus must be a
/// deliberate, reviewed edit rather than a side effect of regenerating it.
///
/// The digest above detects a substituted corpus but not a smaller one: an author
/// who shrinks the generator gets a digest mismatch, is told to update the
/// constant, updates it, and the tool passes over the smaller corpus. A reviewer
/// demonstrated it -- one `.take 1` plus a digest update turned 1085 encodings
/// into 1 and still reported no disagreement. `docs/VALIDATION.md` section 7's
/// ratchet is meant to prevent exactly that, and this is it applied to corpora.
const EXPECTED_ROWS: usize = 1117;

/// Disagreements that were investigated and found to be NASM canonicalising an
/// address rather than Grass encoding it wrongly. `docs/VALIDATION.md` section 2
/// requires disagreement to be "preserved as a finding", so these are listed with
/// their evidence and reported every run rather than filtered out silently.
///
/// Each entry needs the exact source line, both encodings, and a reason that
/// says how the equivalence was established -- not an assertion that it is fine.
const KNOWN_CANONICALISATIONS: [(&str, &str, &str, &str); 1] = [(
    "lea rax, [nosplit r12*1+0x11223344]",
    "4a8d042544332211",
    "498d842444332211",
    "Grass encodes [r12*1+d] as a scaled index with no base (SIB index=100 \
     with REX.X=1, base=101, mod=00). NASM emits the base form (SIB base=100 \
     with REX.B=1, index=100 meaning none, mod=10) and does so even under \
     `nosplit`, which suppresses the reg*2 -> reg+reg split but not this \
     rewrite. Both are 8 bytes and denote the same address. Verified with \
     ndisasm -b 64: 4A8D042544332211 and 498D842444332211 both disassemble \
     to `lea rax,[r12+0x11223344]`.",
)];

/// One corpus row: the bytes Grass emitted and the NASM source they claim to be.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    bytes: Vec<u8>,
    source: String,
}

/// A row where Grass and NASM disagreed, or where NASM produced nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Finding {
    source: String,
    grass_hex: String,
    nasm_hex: String,
}

// ---------------------------------------------------------------------------
// Corpus coverage digest
// ---------------------------------------------------------------------------

/// The NASM source. The other column is the bytes Grass emitted.
fn coverage_of(line: &str) -> &str {
    match line.split('\t').nth(1) {
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

/// Split the corpus into rows, rejecting anything that is not `<hex>TAB<source>`.
///
/// Blank lines are skipped because the Lean generator's own trailing newline
/// produces one; every other line must parse, since a row this tool cannot read
/// is a row it would otherwise silently stop checking.
fn parse_corpus(text: &str) -> Result<Vec<Row>, String> {
    let mut rows = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let (hexbytes, source) = line.split_once('\t').ok_or_else(|| {
            format!(
                "malformed corpus line, expected 2 fields: {}",
                py_repr(line)
            )
        })?;
        rows.push(Row {
            bytes: from_hex(hexbytes)
                .ok_or_else(|| format!("corpus line has non-hex bytes: {}", py_repr(line)))?,
            source: source.to_string(),
        });
    }
    Ok(rows)
}

// ---------------------------------------------------------------------------
// NASM
// ---------------------------------------------------------------------------

fn find_nasm() -> PathBuf {
    if let Some(found) = which("nasm") {
        return found;
    }
    // NASM's Windows installer does not add itself to PATH.
    for candidate in [
        home_dir().map(|h| h.join("AppData/Local/bin/NASM/nasm.exe")),
        Some(PathBuf::from("C:/Program Files/NASM/nasm.exe")),
        Some(PathBuf::from("C:/Program Files (x86)/NASM/nasm.exe")),
    ]
    .into_iter()
    .flatten()
    {
        if candidate.exists() {
            return candidate;
        }
    }
    die("nasm not found on PATH or in the usual install locations");
}

/// A listing line is: line number, address, hex bytes, then the source. A long
/// instruction wraps onto a continuation line carrying the same line number, with
/// the first part ending in "-". Warning lines put asterisks in the byte column.
fn listing_re() -> Regex {
    Regex::new(r"^\s*(\d+)\s+[0-9A-F]{8}\s+([0-9A-F]+-?)\s*(.*)$").expect("static regex")
}

/// Turn a NASM listing into the bytes it assembled for each corpus row.
///
/// Keyed by corpus index rather than by listing line so that the caller never has
/// to know about the prologue; listing line numbers are 1-based and include it.
fn parse_listing(listing: &str) -> Result<BTreeMap<usize, Vec<u8>>, String> {
    let re = listing_re();
    let mut by_line: BTreeMap<usize, String> = BTreeMap::new();
    for raw in listing.lines() {
        let raw = raw.replace('\r', "");
        let Some(caps) = re.captures(&raw) else {
            continue;
        };
        let lineno: usize = caps[1]
            .parse()
            .map_err(|_| format!("listing line number out of range: {}", py_repr(&caps[1])))?;
        let chunk = caps[2].trim_end_matches('-');
        by_line.entry(lineno).or_default().push_str(chunk);
    }

    let mut assembled = BTreeMap::new();
    for (lineno, hexed) in by_line {
        if lineno <= PROLOGUE.len() {
            continue;
        }
        let bytes = from_hex(&hexed)
            .ok_or_else(|| format!("listing line {lineno} has unreadable bytes: {hexed}"))?;
        assembled.insert(lineno - 1 - PROLOGUE.len(), bytes);
    }
    Ok(assembled)
}

/// Assemble each source line, returning its bytes keyed by corpus index.
///
/// A listing is used rather than the flat binary because instruction lengths
/// are exactly what may disagree: walking Grass's own lengths through NASM's
/// output desynchronises after the first difference and reports every later
/// instruction as wrong. The listing gives NASM's own per-line boundaries, so a
/// length disagreement stays local and is reported as itself.
fn assemble(nasm: &Path, sources: &[&str]) -> Option<BTreeMap<usize, Vec<u8>>> {
    let tmp = match tempfile::tempdir() {
        Ok(tmp) => tmp,
        Err(e) => die(&format!("could not create a temporary directory: {e}")),
    };
    let src = tmp.path().join("corpus.asm");
    let lst = tmp.path().join("corpus.lst");
    let out = tmp.path().join("corpus.bin");

    let mut text = String::new();
    for line in PROLOGUE.iter().copied().chain(sources.iter().copied()) {
        // The Python original wrote this file with an ASCII codec, so a
        // non-ASCII source line failed loudly rather than reaching NASM as
        // mojibake. Keep that: a corpus row this tool cannot represent is a row
        // whose verdict would be meaningless.
        if !line.is_ascii() {
            die(&format!(
                "corpus source line is not ASCII: {}",
                py_repr(line)
            ));
        }
        text.push_str(line);
        text.push('\n');
    }
    if let Err(e) = std::fs::write(&src, text) {
        die(&format!("could not write {}: {e}", src.display()));
    }

    let result = match Command::new(nasm)
        .args(["-f", "bin", "-l"])
        .arg(&lst)
        .arg("-o")
        .arg(&out)
        .arg(&src)
        .output()
    {
        Ok(result) => result,
        Err(e) => die(&format!("could not run {}: {e}", nasm.display())),
    };
    if !result.status.success() {
        eprintln!("{}", String::from_utf8_lossy(&result.stderr).trim());
        return None;
    }

    // NASM writes the listing in whatever encoding the source was; anything it
    // could not round-trip is replaced rather than fatal, matching the Python.
    let raw = std::fs::read(&lst).unwrap_or_default();
    let listing = String::from_utf8_lossy(&raw).into_owned();
    match parse_listing(&listing) {
        Ok(assembled) => Some(assembled),
        Err(e) => die(&e),
    }
}

// ---------------------------------------------------------------------------
// Comparison and report
// ---------------------------------------------------------------------------

fn known_canonicalisation(finding: &Finding) -> Option<&'static str> {
    KNOWN_CANONICALISATIONS
        .iter()
        .find(|(source, grass, nasm, _)| {
            *source == finding.source && *grass == finding.grass_hex && *nasm == finding.nasm_hex
        })
        .map(|(_, _, _, reason)| *reason)
}

/// Split the rows into unexplained mismatches and known canonicalisations.
///
/// A row NASM produced no bytes for is a mismatch, not a skip: silence from the
/// oracle is the one outcome an encoder bug could most easily hide behind.
fn classify(rows: &[Row], assembled: &BTreeMap<usize, Vec<u8>>) -> (Vec<Finding>, Vec<Finding>) {
    let mut mismatches = Vec::new();
    let mut canonicalisations = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        match assembled.get(&index) {
            None => mismatches.push(Finding {
                source: row.source.clone(),
                grass_hex: hex_of(&row.bytes),
                nasm_hex: "<no bytes in listing>".to_string(),
            }),
            Some(actual) if *actual != row.bytes => {
                let finding = Finding {
                    source: row.source.clone(),
                    grass_hex: hex_of(&row.bytes),
                    nasm_hex: hex_of(actual),
                };
                if known_canonicalisation(&finding).is_some() {
                    canonicalisations.push(finding);
                } else {
                    mismatches.push(finding);
                }
            }
            Some(_) => {}
        }
    }
    (mismatches, canonicalisations)
}

/// The human-readable verdict and the exit status that goes with it.
///
/// Returned as text rather than printed so the exit-status decision can be
/// tested without an assembler on the machine running the tests.
fn report(rows: usize, mismatches: &[Finding], canonicalisations: &[Finding]) -> (String, i32) {
    let identical = rows - mismatches.len() - canonicalisations.len();
    let mut out = format!(
        "x86 NASM differential: {rows} encodings, {identical} byte-identical, {} known canonicalisation(s), {} unexplained\n",
        canonicalisations.len(),
        mismatches.len()
    );

    for finding in canonicalisations {
        out.push_str(&format!("\n  canonicalisation: {}\n", finding.source));
        out.push_str(&format!("    grass: {}\n", finding.grass_hex));
        out.push_str(&format!("    nasm : {}\n", finding.nasm_hex));
        let reason = known_canonicalisation(finding).unwrap_or("");
        out.push_str(&format!("    {reason}\n"));
    }

    if !mismatches.is_empty() {
        out.push_str(&format!("\n{} mismatch(es):\n\n", mismatches.len()));
        for finding in mismatches.iter().take(40) {
            out.push_str(&format!("  {}\n", finding.source));
            out.push_str(&format!("    grass: {}\n", finding.grass_hex));
            out.push_str(&format!("    nasm : {}\n", finding.nasm_hex));
        }
        if mismatches.len() > 40 {
            out.push_str(&format!("  ... and {} more\n", mismatches.len() - 40));
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
        // The Python original named itself `x86-nasm-differential.py` here. That
        // is the one place this port does not reproduce its text: a message
        // telling the reader to run a file that is no longer the tool sends them
        // looking for the wrong thing.
        die("usage: x86-nasm-differential <corpus.txt>");
    }
    // Located before the corpus is read, as in the Python: a missing assembler
    // is a hard failure, so there is no point reporting corpus problems first.
    let nasm = find_nasm();

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

    let sources: Vec<&str> = rows.iter().map(|r| r.source.as_str()).collect();
    let Some(assembled) = assemble(&nasm, &sources) else {
        return 1;
    };

    let (mismatches, canonicalisations) = classify(&rows, &assembled);
    let (text, code) = report(rows.len(), &mismatches, &canonicalisations);
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

/// Python's `repr` of a string, for the malformed-line messages. Reproduced so
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
    // are consulted so the same binary finds NASM on a developer's machine and
    // in the Linux CI job.
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

    fn row(bytes: &str, source: &str) -> Row {
        Row {
            bytes: from_hex(bytes).unwrap(),
            source: source.to_string(),
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
    fn parses_two_column_rows() {
        let rows = parse_corpus("4889c8\tmov rax, rcx\n90\tnop\n").unwrap();
        assert_eq!(rows, vec![row("4889c8", "mov rax, rcx"), row("90", "nop")]);
    }

    #[test]
    fn blank_and_whitespace_only_lines_are_skipped() {
        // The Lean generator's trailing newline produces one of these every run,
        // so skipping them is load-bearing rather than defensive.
        let rows = parse_corpus("\n90\tnop\n   \n\t\n90\tnop\n").unwrap();
        assert_eq!(rows.len(), 2);
    }

    #[test]
    fn a_line_without_a_tab_is_rejected() {
        let err = parse_corpus("90nop\n").unwrap_err();
        assert!(err.contains("expected 2 fields"), "{err}");
        assert!(err.contains("'90nop'"), "{err}");
    }

    #[test]
    fn a_line_with_unreadable_hex_is_rejected() {
        assert!(parse_corpus("9\tnop\n").unwrap_err().contains("non-hex"));
        assert!(parse_corpus("9z\tnop\n").unwrap_err().contains("non-hex"));
    }

    #[test]
    fn extra_tabs_belong_to_the_source_column() {
        // NASM sources can contain a tab; only the first separates the columns.
        let rows = parse_corpus("90\tnop\tafter\n").unwrap();
        assert_eq!(rows[0].source, "nop\tafter");
    }

    #[test]
    fn digest_ignores_the_byte_column() {
        // The whole point of the coverage digest: changing what Grass emitted
        // must reach the oracle rather than being intercepted by the guard.
        let before = corpus_digest("4889c8\tmov rax, rcx\n90\tnop\n");
        let after = corpus_digest("0000\tmov rax, rcx\n00\tnop\n");
        assert_eq!(before, after);
    }

    #[test]
    fn digest_notices_dropped_and_reordered_rows() {
        let full = corpus_digest("90\tnop\n91\txchg\n");
        assert_ne!(full, corpus_digest("90\tnop\n"));
        assert_ne!(full, corpus_digest("91\txchg\n90\tnop\n"));
        assert_ne!(full, corpus_digest("90\tnop\n91\txchg\n90\tnop\n"));
    }

    #[test]
    fn digest_is_independent_of_line_endings() {
        assert_eq!(
            corpus_digest("90\tnop\n91\txchg\n"),
            corpus_digest("90\tnop\r\n91\txchg\r\n")
        );
    }

    #[test]
    fn coverage_of_a_column_less_line_is_the_whole_line() {
        assert_eq!(coverage_of("no tabs here"), "no tabs here");
    }

    #[test]
    fn listing_lines_are_keyed_by_corpus_index() {
        // Line 3 is the first corpus row, because the prologue occupies 1 and 2.
        let listing = "     1                                  BITS 64\n\
                            2                                  DEFAULT ABS\n\
                            3 00000000 488D8044332211          lea rax, [rax+0x11223344]\n";
        let assembled = parse_listing(listing).unwrap();
        assert_eq!(assembled.len(), 1);
        assert_eq!(assembled[&0], from_hex("488d8044332211").unwrap());
    }

    #[test]
    fn wrapped_listing_lines_are_rejoined() {
        // A long instruction wraps with a trailing "-" and repeats its line
        // number; treating the parts as separate rows would report a length that
        // no assembler ever produced.
        let listing = "     3 00000000 48B8887766554433-       mov rax, 0x1122334455667788\n\
                            3 00000008 2211\n";
        let assembled = parse_listing(listing).unwrap();
        assert_eq!(assembled[&0], from_hex("48b88877665544332211").unwrap());
    }

    #[test]
    fn listing_noise_is_ignored() {
        // Warning lines put asterisks in the byte column and must not become rows.
        let listing = "corpus.asm:3: warning: something\n\
                            3 00000000 ******************      lea rax, [rax+1]\n\
                       not a listing line at all\n";
        assert!(parse_listing(listing).unwrap().is_empty());
    }

    #[test]
    fn identical_bytes_are_not_findings() {
        let rows = vec![row("90", "nop")];
        let assembled = BTreeMap::from([(0, from_hex("90").unwrap())]);
        let (mismatches, canon) = classify(&rows, &assembled);
        assert!(mismatches.is_empty() && canon.is_empty());
    }

    #[test]
    fn differing_bytes_are_a_mismatch() {
        let rows = vec![row("90", "nop")];
        let assembled = BTreeMap::from([(0, from_hex("91").unwrap())]);
        let (mismatches, canon) = classify(&rows, &assembled);
        assert!(canon.is_empty());
        assert_eq!(mismatches[0].grass_hex, "90");
        assert_eq!(mismatches[0].nasm_hex, "91");
    }

    #[test]
    fn a_row_nasm_produced_nothing_for_is_a_mismatch() {
        let rows = vec![row("90", "nop")];
        let (mismatches, _) = classify(&rows, &BTreeMap::new());
        assert_eq!(mismatches[0].nasm_hex, "<no bytes in listing>");
    }

    #[test]
    fn the_known_canonicalisation_is_recognised_and_still_reported() {
        let (source, grass, nasm, _) = KNOWN_CANONICALISATIONS[0];
        let rows = vec![row(grass, source)];
        let assembled = BTreeMap::from([(0, from_hex(nasm).unwrap())]);
        let (mismatches, canon) = classify(&rows, &assembled);
        assert!(mismatches.is_empty());
        assert_eq!(canon.len(), 1);

        let (text, code) = report(1, &mismatches, &canon);
        assert_eq!(
            code, 0,
            "a documented canonicalisation must not fail the run"
        );
        assert!(text.contains("1 known canonicalisation(s), 0 unexplained"));
        assert!(text.contains("  canonicalisation: lea rax, [nosplit"));
        assert!(
            text.contains("ndisasm -b 64"),
            "the evidence must be printed"
        );
        assert!(text.ends_with("no disagreement\n"));
    }

    #[test]
    fn a_canonicalisation_only_counts_for_its_exact_encodings() {
        // Matching on the source line alone would let a real encoder change hide
        // behind the excuse written for a different pair of bytes.
        let (source, grass, _, _) = KNOWN_CANONICALISATIONS[0];
        let rows = vec![row(grass, source)];
        let assembled = BTreeMap::from([(0, from_hex("90").unwrap())]);
        let (mismatches, canon) = classify(&rows, &assembled);
        assert!(canon.is_empty());
        assert_eq!(mismatches.len(), 1);
    }

    #[test]
    fn a_clean_run_exits_zero() {
        let (text, code) = report(1117, &[], &[]);
        assert_eq!(code, 0);
        assert_eq!(
            text,
            "x86 NASM differential: 1117 encodings, 1117 byte-identical, \
             0 known canonicalisation(s), 0 unexplained\nno disagreement\n"
        );
    }

    #[test]
    fn any_mismatch_exits_one() {
        let mismatches = vec![Finding {
            source: "nop".to_string(),
            grass_hex: "90".to_string(),
            nasm_hex: "91".to_string(),
        }];
        let (text, code) = report(2, &mismatches, &[]);
        assert_eq!(code, 1);
        assert!(text.contains("2 encodings, 1 byte-identical"), "{text}");
        assert!(text.contains("\n1 mismatch(es):\n\n  nop\n    grass: 90\n    nasm : 91\n"));
        assert!(!text.contains("no disagreement"));
    }

    #[test]
    fn long_mismatch_lists_are_truncated_with_a_count() {
        let mismatches: Vec<Finding> = (0..45)
            .map(|i| Finding {
                source: format!("row{i}"),
                grass_hex: "90".to_string(),
                nasm_hex: "91".to_string(),
            })
            .collect();
        let (text, code) = report(45, &mismatches, &[]);
        assert_eq!(code, 1);
        assert!(text.contains("  row39\n"));
        assert!(!text.contains("  row40\n"));
        assert!(text.contains("  ... and 5 more\n"));
    }

    #[test]
    fn py_repr_quotes_the_way_python_did() {
        assert_eq!(py_repr("plain"), "'plain'");
        assert_eq!(py_repr("a\tb"), "'a\\tb'");
        assert_eq!(py_repr("it's"), "\"it's\"");
        assert_eq!(py_repr("it's \"q\""), "'it\\'s \"q\"'");
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
