//! Differential check of Grass's Win64 unwind metadata against MASM.
//!
//! `docs/VALIDATION.md` section 2 layer 2 asks for comparison against
//! independent tools "where independent tools exist". For `.xdata` the tool is
//! Microsoft's own assembler. MASM's `PROC FRAME` plus
//! `.pushreg`/`.allocstack`/`.setframe` makes `ml64.exe` generate an
//! `UNWIND_INFO` structure from a prologue, which is exactly what
//! `Grass.ABI.Win64.UnwindInfo.toBytes` produces.
//!
//! This oracle is stronger than the NASM one used for instruction encodings.
//! NASM is a third party that agrees with Grass about Intel's documented
//! format; `ml64` is the vendor of the format being modelled. A disagreement
//! here is much more likely to be a Grass defect than an oracle defect -- but
//! it is still not authority. `docs/VALIDATION.md` section 2: "Tools and
//! hardware are fallible oracles. Disagreement is preserved as a finding;
//! majority vote does not establish truth."
//!
//! What each row checks is wider than the byte layout. The corpus computes each
//! `UNWIND_CODE`'s prologue offset from Grass's belief about instruction
//! lengths -- that a push of `r12` is two bytes and a push of `rbx` is one,
//! that `sub rsp, 32` is four bytes and `sub rsp, 136` is seven. `ml64` derives
//! the same offsets from the instructions it actually assembled, so a wrong
//! length model fails the row even though this code path never encodes an
//! instruction.
//!
//! Exit status is 1 on any mismatch, and also on an oracle that could not be
//! run: a check that silently passes because the assembler was missing is worse
//! than no check, so a missing `ml64.exe` is a failure rather than a skip.
//!
//! `.xdata` is read out of the COFF object directly rather than through
//! `dumpbin /rawdata`, because `dumpbin` prints raw data grouped into
//! little-endian words -- with the default grouping the bytes come back in an
//! order that is not the file order, which is a good way to confirm a byte
//! layout that is in fact reversed.
//!
//! This is a port of `Tools/win64-unwind-differential.py`. The parity bar is
//! behavioural: the same arguments, the same text on the same stream, and the
//! same exit status, so that a reader who knows the old tool's report can read
//! this one's without relearning it.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The rationale above, in the exact shape the Python original printed when it
/// was invoked with the wrong number of arguments (it printed its own module
/// docstring). It is duplicated rather than derived because a Rust doc comment
/// is not readable at run time; the two must be edited together.
///
/// The one deliberate difference from the Python text is the invocation line,
/// which names this binary. Pointing a reader at a script that no longer runs
/// the check would be worse than the divergence.
const USAGE_DOC: &str = r#"Differential check of Grass's Win64 unwind metadata against MASM.

`docs/VALIDATION.md` section 2 layer 2 asks for comparison against independent
tools "where independent tools exist". For `.xdata` the tool is Microsoft's own
assembler. MASM's `PROC FRAME` plus `.pushreg`/`.allocstack`/`.setframe` makes
`ml64.exe` generate an `UNWIND_INFO` structure from a prologue, which is exactly
what `Grass.ABI.Win64.UnwindInfo.toBytes` produces.

This oracle is stronger than the NASM one used for instruction encodings. NASM
is a third party that agrees with Grass about Intel's documented format; `ml64`
is the vendor of the format being modelled. A disagreement here is much more
likely to be a Grass defect than an oracle defect -- but it is still not
authority. `docs/VALIDATION.md` section 2: "Tools and hardware are fallible
oracles. Disagreement is preserved as a finding; majority vote does not
establish truth."

What each row checks is wider than the byte layout. The corpus computes each
`UNWIND_CODE`'s prologue offset from Grass's belief about instruction lengths --
that a push of `r12` is two bytes and a push of `rbx` is one, that `sub rsp, 32`
is four bytes and `sub rsp, 136` is seven. `ml64` derives the same offsets from
the instructions it actually assembled, so a wrong length model fails the row
even though this code path never encodes an instruction.

Usage:
    lake env lean --run Tests/ABI/Win64/UnwindCorpus.lean > corpus.txt
    win64-unwind-differential corpus.txt

Exit status is 1 on any mismatch, and also on an oracle that could not be run:
a check that silently passes because the assembler was missing is worse than no
check, so a missing `ml64.exe` is a failure rather than a skip.

`.xdata` is read out of the COFF object directly rather than through
`dumpbin /rawdata`, because `dumpbin` prints raw data grouped into little-endian
words -- with the default grouping the bytes come back in an order that is not
the file order, which is a good way to confirm a byte layout that is in fact
reversed.
"#;

/// The corpus this tool was reviewed against, as a digest of its content.
///
/// A row count is not enough: a corpus of one row, or one whose every row is a
/// copy of the first, has a plausible count and checks nothing. Binding content
/// means substituting a same-length corpus fails. Changing the corpus requires
/// updating this constant, which is the reviewed edit `docs/VALIDATION.md`
/// section 7 asks for rather than a silent change to what is being checked.
const EXPECTED_DIGEST: &str = "a9009d55a935a81f1ca90da712f308d2a5d34722dfa0bbe8fb7f331858755447";

/// The coverage this tool was reviewed at. Shrinking the corpus must be a
/// deliberate, reviewed edit rather than a side effect of regenerating it.
///
/// The digest above detects a substituted corpus but not a smaller one: an
/// author who shrinks the generator gets a digest mismatch, is told to update
/// the constant, updates it, and the tool passes over the smaller corpus. A
/// reviewer demonstrated it -- one `.take 1` plus a digest update turned 1085
/// encodings into 1 and still reported no disagreement. `docs/VALIDATION.md`
/// section 7's ratchet is meant to prevent exactly that, and this is it applied
/// to corpora.
const EXPECTED_ROWS: usize = 52;

// ---------------------------------------------------------------------------
// SHA-256
// ---------------------------------------------------------------------------

/// SHA-256, because `EXPECTED_DIGEST` above is a reviewed constant produced by
/// `hashlib.sha256` and has to keep meaning the same thing across the port.
///
/// Written out here rather than taken from a crate for the reason
/// `lakefile.toml` gives for Lean dependencies: `docs/FOUNDATION.md` puts every
/// selected dependency into the trust ledger, so a dependency is a reviewed
/// change and not a convenience. The same routine appears in
/// `x86_machine_probe.rs`; the binaries are deliberately self-contained so that
/// a change to one cannot alter the other's verdict.
mod sha256 {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    /// The lowercase hex digest of `data`, matching `hashlib.sha256(...).hexdigest()`.
    pub fn hex(data: &[u8]) -> String {
        let mut h: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        let bit_len = (data.len() as u64).wrapping_mul(8);
        let mut msg = Vec::with_capacity(data.len() + 72);
        msg.extend_from_slice(data);
        msg.push(0x80);
        while msg.len() % 64 != 56 {
            msg.push(0);
        }
        msg.extend_from_slice(&bit_len.to_be_bytes());

        for chunk in msg.chunks_exact(64) {
            let mut w = [0u32; 64];
            for (i, word) in w.iter_mut().enumerate().take(16) {
                let b = &chunk[i * 4..i * 4 + 4];
                *word = u32::from_be_bytes([b[0], b[1], b[2], b[3]]);
            }
            for i in 16..64 {
                let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
                let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16]
                    .wrapping_add(s0)
                    .wrapping_add(w[i - 7])
                    .wrapping_add(s1);
            }
            let mut v = h;
            for (kv, wv) in K.iter().zip(w.iter()) {
                let s1 = v[4].rotate_right(6) ^ v[4].rotate_right(11) ^ v[4].rotate_right(25);
                let ch = (v[4] & v[5]) ^ ((!v[4]) & v[6]);
                let t1 = v[7]
                    .wrapping_add(s1)
                    .wrapping_add(ch)
                    .wrapping_add(*kv)
                    .wrapping_add(*wv);
                let s0 = v[0].rotate_right(2) ^ v[0].rotate_right(13) ^ v[0].rotate_right(22);
                let maj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
                let t2 = s0.wrapping_add(maj);
                v[7] = v[6];
                v[6] = v[5];
                v[5] = v[4];
                v[4] = v[3].wrapping_add(t1);
                v[3] = v[2];
                v[2] = v[1];
                v[1] = v[0];
                v[0] = t1.wrapping_add(t2);
            }
            for (acc, add) in h.iter_mut().zip(v.iter()) {
                *acc = acc.wrapping_add(*add);
            }
        }

        let mut out = String::with_capacity(64);
        for word in h {
            out.push_str(&format!("{word:08x}"));
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Text handling, matching Python's
// ---------------------------------------------------------------------------

/// Python's universal newlines, which `Path.read_text` applies before any of
/// this tool's parsing sees the corpus. A corpus written on Windows arrives
/// with `\r\n` and must hash the same as one written on Linux, so the
/// translation has to happen here too rather than being left to `\r`-stripping
/// further down.
fn universal_newlines(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\r' {
            if chars.peek() == Some(&'\n') {
                chars.next();
            }
            out.push('\n');
        } else {
            out.push(c);
        }
    }
    out
}

/// `str.splitlines`, whose line boundaries are wider than `\n`.
///
/// Reproduced rather than approximated with `str::lines` because the difference
/// is observable: a corpus containing a vertical tab splits into more lines in
/// Python, each of which then fails the three-field check. Matching means a
/// malformed corpus is rejected here for the same reason it was there.
fn python_splitlines(text: &str) -> Vec<&str> {
    const BOUNDARIES: [char; 10] = [
        '\n', '\r', '\x0b', '\x0c', '\x1c', '\x1d', '\x1e', '\u{85}', '\u{2028}', '\u{2029}',
    ];
    let mut out = Vec::new();
    let mut start = 0usize;
    let mut i = 0usize;
    let bytes = text.as_bytes();
    while i < text.len() {
        let c = text[i..].chars().next().expect("i is a char boundary");
        let width = c.len_utf8();
        if !BOUNDARIES.contains(&c) {
            i += width;
            continue;
        }
        out.push(&text[start..i]);
        let mut next = i + width;
        // `\r\n` is one boundary, not two.
        if c == '\r' && bytes.get(next) == Some(&b'\n') {
            next += 1;
        }
        start = next;
        i = next;
    }
    if start < text.len() {
        out.push(&text[start..]);
    }
    out
}

/// Python's `repr` of a string, for the malformed-row message. The quoting
/// matters: a row whose fields are separated by spaces rather than tabs is
/// indistinguishable from a well-formed one unless the message shows the
/// escapes.
fn python_repr(s: &str) -> String {
    let quote = if s.contains('\'') && !s.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut out = String::with_capacity(s.len() + 2);
    out.push(quote);
    for c in s.chars() {
        match c {
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

// ---------------------------------------------------------------------------
// Corpus
// ---------------------------------------------------------------------------

/// The prologue's name and its MASM text. The first column is the `.xdata`
/// Grass predicted.
fn coverage_of(line: &str) -> String {
    let fields: Vec<&str> = line.split('\t').collect();
    if fields.len() > 1 {
        fields[1..].join("\t")
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
/// row-count weakness described on `EXPECTED_ROWS`, one column over.
///
/// Hashing coverage keeps what the guard is for. A corpus that drops rows,
/// duplicates them, or swaps hard cases for easy ones still changes this
/// digest; a corpus whose byte column changed because the encoder changed does
/// not, and goes straight to the oracle that can judge it.
fn corpus_digest(text: &str) -> String {
    let normalised = python_splitlines(text)
        .into_iter()
        .filter(|line| !line.trim().is_empty())
        .map(|line| coverage_of(line.trim_end_matches('\r')))
        .collect::<Vec<_>>()
        .join("\n");
    sha256::hex(normalised.as_bytes())
}

/// One corpus row: the `.xdata` Grass predicts, a label, and the MASM prologue.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    expected_hex: String,
    name: String,
    masm: String,
}

/// Parse the corpus, or the message explaining why it is not usable.
///
/// Blank lines are skipped and everything else must have exactly three fields:
/// a row with a missing column is a generator defect, and guessing which column
/// went missing would turn it into a silent coverage loss.
fn parse_rows(text: &str) -> Result<Vec<Row>, String> {
    let mut rows = Vec::new();
    for line in python_splitlines(text) {
        if line.trim().is_empty() {
            continue;
        }
        let fields: Vec<&str> = line.trim_end_matches('\r').split('\t').collect();
        if fields.len() != 3 {
            return Err(format!("malformed corpus row: {}", python_repr(line)));
        }
        rows.push(Row {
            expected_hex: fields[0].to_string(),
            name: fields[1].to_string(),
            masm: fields[2].to_string(),
        });
    }
    Ok(rows)
}

/// The checks that must pass before the oracle is worth starting, in the order
/// the Python original ran them: digest first, then shape, then size. The order
/// is observable, because only the first failure is reported.
fn preflight(text: &str) -> Result<Vec<Row>, String> {
    let actual_digest = corpus_digest(text);
    if actual_digest != EXPECTED_DIGEST {
        return Err(format!(
            "corpus digest {actual_digest} does not match the reviewed \
             {EXPECTED_DIGEST}. Regenerate it from the Lean corpus, or update \
             EXPECTED_DIGEST here if the corpus genuinely changed."
        ));
    }
    let rows = parse_rows(text)?;
    if rows.is_empty() {
        return Err("corpus is empty".to_string());
    }
    if rows.len() < EXPECTED_ROWS {
        return Err(format!(
            "corpus has {} rows, fewer than the {EXPECTED_ROWS} this tool was \
             reviewed against. Coverage may only grow; if the reduction is \
             deliberate, lower EXPECTED_ROWS in the same reviewed edit that \
             shrinks the corpus.",
            rows.len()
        ));
    }
    Ok(rows)
}

// ---------------------------------------------------------------------------
// Assembling one prologue
// ---------------------------------------------------------------------------

/// Undo the prologue, so the emitted procedure is not obvious nonsense.
///
/// `ml64` builds `UNWIND_INFO` from the directives and does not check the
/// epilogue, so this affects nothing that is being measured. It is here so the
/// corpus does not depend on that being true.
fn epilogue_for(steps: &[&str]) -> String {
    let mut out = Vec::new();
    for text in steps.iter().rev() {
        if let Some(rest) = text.strip_prefix("push ") {
            out.push(format!("    pop {rest}"));
        } else if let Some(rest) = text.strip_prefix("sub rsp, ") {
            out.push(format!("    add rsp, {rest}"));
        }
    }
    out.join("\n")
}

/// The MASM source for one corpus row.
///
/// The `" | "`-separated prologue is instructions and directives alternating;
/// the directives are the half `ml64` turns into `UNWIND_INFO`, and the
/// instructions are the half whose lengths decide the offsets it records.
fn masm_source(masm: &str) -> String {
    let parts: Vec<&str> = masm.split('|').map(|p| p.trim()).collect();
    let instructions: Vec<&str> = parts
        .iter()
        .copied()
        .filter(|p| !p.starts_with('.'))
        .collect();
    let prologue = parts
        .iter()
        .map(|p| format!("    {p}"))
        .collect::<Vec<_>>()
        .join("\n");
    let epilogue = epilogue_for(&instructions);
    format!(
        ".CODE\n\
         grassprobe PROC FRAME\n\
         {prologue}\n\
         \x20   .endprolog\n\
         \x20   xor eax, eax\n\
         {epilogue}\n\
         \x20   ret\n\
         grassprobe ENDP\n\
         END\n"
    )
}

/// A file name that survives being written to disk, from a corpus label that
/// need not.
fn safe_name(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Read the `.xdata` section's raw bytes out of a COFF object.
fn xdata_of(data: &[u8]) -> Option<&[u8]> {
    if data.len() < 20 {
        return None;
    }
    let n_sections = u16::from_le_bytes([data[2], data[3]]) as usize;
    let opt_size = u16::from_le_bytes([data[16], data[17]]) as usize;
    let base = 20 + opt_size;
    for i in 0..n_sections {
        let off = base + i * 40;
        if off + 40 > data.len() {
            return None;
        }
        let raw = &data[off..off + 8];
        let end = raw.iter().rposition(|b| *b != 0).map_or(0, |p| p + 1);
        // COFF section names are bytes, not text; `latin-1` is Python's way of
        // spelling "one byte, one character" and is reproduced by comparing
        // bytes directly.
        if &raw[..end] != b".xdata" {
            continue;
        }
        let size = u32::from_le_bytes([
            data[off + 16],
            data[off + 17],
            data[off + 18],
            data[off + 19],
        ]) as usize;
        let ptr = u32::from_le_bytes([
            data[off + 20],
            data[off + 21],
            data[off + 22],
            data[off + 23],
        ]) as usize;
        if ptr == 0 || ptr + size > data.len() {
            return None;
        }
        return Some(&data[ptr..ptr + size]);
    }
    None
}

fn hex_of(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// Collapse a captured child stream the way Python's `text=True` did, so a
/// multi-line `ml64` diagnostic reads as one line in the report.
fn collapse_detail(stdout: &[u8], stderr: &[u8]) -> String {
    let joined = format!(
        "{}{}",
        String::from_utf8_lossy(stdout),
        String::from_utf8_lossy(stderr)
    );
    let detail = universal_newlines(&joined).trim().replace('\n', "; ");
    detail.chars().take(300).collect()
}

/// Assemble one prologue and return its `.xdata` bytes.
fn assemble(ml64: &str, workdir: &Path, name: &str, masm: &str) -> Result<Vec<u8>, String> {
    let source = masm_source(masm);
    let asm = workdir.join(format!("{name}.asm"));
    let obj = workdir.join(format!("{name}.obj"));
    if let Err(e) = std::fs::write(&asm, source.as_bytes()) {
        return Err(format!("could not write {}: {e}", asm.display()));
    }
    let output = Command::new(ml64)
        .args(["/nologo", "/c", "/Fo"])
        .arg(&obj)
        .arg(&asm)
        .current_dir(workdir)
        .output();
    let output = match output {
        Ok(o) => o,
        Err(e) => return Err(format!("ml64 failed: {e}")),
    };
    if !output.status.success() {
        return Err(format!(
            "ml64 failed: {}",
            collapse_detail(&output.stdout, &output.stderr)
        ));
    }
    if !obj.is_file() {
        return Err("ml64 produced no object".to_string());
    }
    let bytes = match std::fs::read(&obj) {
        Ok(b) => b,
        Err(_) => return Err("no .xdata section in the object".to_string()),
    };
    match xdata_of(&bytes) {
        Some(x) => Ok(x.to_vec()),
        None => Err("no .xdata section in the object".to_string()),
    }
}

// ---------------------------------------------------------------------------
// Locating the oracle
// ---------------------------------------------------------------------------

/// Locate an MSVC tool, preferring an explicit environment override.
///
/// MSVC is not on `PATH` unless a developer prompt set it up, so a plain
/// `which` finds nothing on an otherwise perfectly capable machine.
fn find_tool(name: &str) -> Option<String> {
    let var = name.to_uppercase().replace(".EXE", "") + "_PATH";
    if let Some(v) = std::env::var_os(&var) {
        let v = v.to_string_lossy().into_owned();
        if !v.is_empty() && Path::new(&v).is_file() {
            return Some(v);
        }
    }
    let roots = [
        PathBuf::from("C:/Program Files/Microsoft Visual Studio"),
        PathBuf::from("C:/Program Files (x86)/Microsoft Visual Studio"),
    ];
    let mut found: Vec<PathBuf> = Vec::new();
    for root in roots {
        if !root.is_dir() {
            continue;
        }
        // The Python glob was `*/*/VC/Tools/MSVC/*/bin/Hostx64/x64/<name>`:
        // edition year, edition name, then the toolset version.
        for year in visible_dirs(&root) {
            for edition in visible_dirs(&year) {
                let toolsets = edition.join("VC").join("Tools").join("MSVC");
                for toolset in visible_dirs(&toolsets) {
                    let exe = toolset.join("bin").join("Hostx64").join("x64").join(name);
                    if exe.is_file() {
                        found.push(exe);
                    }
                }
            }
        }
    }
    if found.is_empty() {
        return None;
    }
    // Highest MSVC version last in sorted order; prefer the newest.
    //
    // The ordering is `pathlib`'s: paths compare as tuples of case-folded
    // components, not as flat strings, and the two differ here. Whole-string
    // ordering puts `Program Files (x86)` before `Program Files`, because a
    // space sorts below a separator; component ordering puts `Program Files`
    // first, because it is a prefix of the other. The tools this picks are
    // different builds of `ml64`, so the difference is observable, and matching
    // the original means matching the component ordering.
    found.sort_by_key(|p| path_sort_key(p.as_path()));
    found.last().map(|p| p.to_string_lossy().into_owned())
}

/// A path as `pathlib` orders it on Windows: its components, case-folded.
fn path_sort_key(path: &Path) -> Vec<String> {
    path.components()
        .map(|c| c.as_os_str().to_string_lossy().to_lowercase())
        .collect()
}

/// Directory entries a `*` glob would match: real directories, and not the
/// dot-prefixed names `pathlib` treats as hidden.
fn visible_dirs(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    if let Ok(entries) = std::fs::read_dir(root) {
        for entry in entries.flatten() {
            let name = entry.file_name();
            if name.to_string_lossy().starts_with('.') {
                continue;
            }
            let path = entry.path();
            if path.is_dir() {
                out.push(path);
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

/// A row whose `.xdata` `ml64` disagreed with.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Mismatch {
    name: String,
    want: String,
    got: String,
    masm: String,
}

/// What the run produced, split by stream, plus the exit status.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Report {
    stdout: String,
    stderr: String,
    code: i32,
}

/// Turn the run's findings into the report and the verdict.
///
/// An unassembled row counts as a failure and not a skip, for the reason the
/// module docstring gives about a missing oracle: the row was supposed to be
/// checked and was not, and only the exit status can say so.
fn build_report(row_count: usize, mismatches: &[Mismatch], errors: &[(String, String)]) -> Report {
    let mut stderr = String::new();
    for (name, err) in errors {
        stderr.push_str(&format!("ERROR  {name}: {err}\n"));
    }
    for m in mismatches {
        stderr.push_str(&format!("MISMATCH  {}\n", m.name));
        stderr.push_str(&format!("    prologue  {}\n", m.masm));
        stderr.push_str(&format!("    grass     {}\n", m.want));
        stderr.push_str(&format!("    ml64      {}\n", m.got));
    }
    let checked = row_count - errors.len();
    if !mismatches.is_empty() || !errors.is_empty() {
        stderr.push_str(&format!(
            "win64 unwind differential: {row_count} rows, {checked} assembled, \
             {} disagree with ml64, {} could not be assembled\n",
            mismatches.len(),
            errors.len()
        ));
        return Report {
            stdout: String::new(),
            stderr,
            code: 1,
        };
    }
    Report {
        stdout: format!(
            "win64 unwind differential: {row_count} prologues, .xdata \
             byte-identical to ml64 on all of them\n"
        ),
        stderr,
        code: 0,
    }
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

fn main() -> std::process::ExitCode {
    std::process::ExitCode::from(run() as u8)
}

fn run() -> i32 {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        println!("{USAGE_DOC}");
        return 2;
    }

    let raw = match std::fs::read(&args[1]) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("cannot read {}: {e}", args[1]);
            return 1;
        }
    };
    let text = match String::from_utf8(raw) {
        Ok(t) => universal_newlines(&t),
        Err(e) => {
            eprintln!("{} is not valid UTF-8: {e}", args[1]);
            return 1;
        }
    };

    let rows = match preflight(&text) {
        Ok(rows) => rows,
        Err(message) => {
            eprintln!("{message}");
            return 1;
        }
    };

    let ml64 = match find_tool("ml64.exe") {
        Some(p) => p,
        None => {
            eprintln!(
                "ml64.exe not found. Set ML64_PATH, or install the MSVC build \
                 tools. This is a failure rather than a skip: a differential \
                 check that passes because its oracle is absent is worse than \
                 none."
            );
            return 1;
        }
    };

    let tmp = match tempfile::TempDir::new() {
        Ok(t) => t,
        Err(e) => {
            eprintln!("could not create a working directory: {e}");
            return 1;
        }
    };
    let workdir = tmp.path();

    let mut mismatches: Vec<Mismatch> = Vec::new();
    let mut errors: Vec<(String, String)> = Vec::new();
    for row in &rows {
        let safe = safe_name(&row.name);
        match assemble(&ml64, workdir, &safe, &row.masm) {
            Ok(got) => {
                let got_hex = hex_of(&got);
                if got_hex != row.expected_hex {
                    mismatches.push(Mismatch {
                        name: row.name.clone(),
                        want: row.expected_hex.clone(),
                        got: got_hex,
                        masm: row.masm.clone(),
                    });
                }
            }
            Err(err) => errors.push((row.name.clone(), err)),
        }
    }

    let report = build_report(rows.len(), &mismatches, &errors);
    print!("{}", report.stdout);
    eprint!("{}", report.stderr);
    report.code
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_matches_known_vectors() {
        assert_eq!(
            sha256::hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256::hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        // Two blocks, so the padding path that carries the length into a fresh
        // block is exercised rather than only the single-block one.
        assert_eq!(
            sha256::hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    #[test]
    fn universal_newlines_matches_python_text_mode() {
        assert_eq!(universal_newlines("a\r\nb\rc\nd"), "a\nb\nc\nd");
        assert_eq!(universal_newlines("\r\n"), "\n");
        assert_eq!(universal_newlines(""), "");
    }

    #[test]
    fn splitlines_uses_python_boundaries() {
        assert_eq!(python_splitlines("a\nb\nc"), vec!["a", "b", "c"]);
        assert_eq!(python_splitlines("a\nb\n"), vec!["a", "b"]);
        assert_eq!(python_splitlines("a\r\nb"), vec!["a", "b"]);
        // The boundaries `str::lines` would miss.
        assert_eq!(
            python_splitlines("a\x0bb\x0cc\u{85}d"),
            vec!["a", "b", "c", "d"]
        );
        assert!(python_splitlines("").is_empty());
    }

    #[test]
    fn repr_escapes_the_separators_a_reader_needs_to_see() {
        assert_eq!(python_repr("a\tb"), "'a\\tb'");
        assert_eq!(python_repr("a b"), "'a b'");
        assert_eq!(python_repr("it's"), "\"it's\"");
        assert_eq!(python_repr("back\\slash"), "'back\\\\slash'");
    }

    /// The digest is over the coverage columns only, so a change in the bytes
    /// Grass emitted has to reach the oracle instead of being intercepted here.
    #[test]
    fn digest_ignores_the_predicted_bytes_column() {
        let a = "aabb\tpush-rbx\tpush rbx | .pushreg rbx\n";
        let b = "ffff\tpush-rbx\tpush rbx | .pushreg rbx\n";
        assert_eq!(corpus_digest(a), corpus_digest(b));
    }

    /// ...but a corpus that drops a row, or swaps one case for another, does
    /// change it. That is the whole point of the constant.
    #[test]
    fn digest_tracks_coverage_changes() {
        let full = "aa\tone\tpush rbx | .pushreg rbx\nbb\ttwo\tpush rbp | .pushreg rbp\n";
        let shrunk = "aa\tone\tpush rbx | .pushreg rbx\n";
        let swapped = "aa\tone\tpush rbx | .pushreg rbx\nbb\ttwo\tpush r12 | .pushreg r12\n";
        assert_ne!(corpus_digest(full), corpus_digest(shrunk));
        assert_ne!(corpus_digest(full), corpus_digest(swapped));
    }

    /// Line endings must not change the digest, or the constant would depend on
    /// which platform regenerated the corpus.
    #[test]
    fn digest_is_line_ending_agnostic() {
        let unix = "aa\tone\tpush rbx | .pushreg rbx\nbb\ttwo\tpush rbp | .pushreg rbp\n";
        let dos = universal_newlines(
            "aa\tone\tpush rbx | .pushreg rbx\r\nbb\ttwo\tpush rbp | .pushreg rbp\r\n",
        );
        assert_eq!(corpus_digest(unix), corpus_digest(&dos));
    }

    /// A digest computed by `hashlib.sha256` in the Python original, over a
    /// corpus small enough to write down. This pins the whole chain -- coverage
    /// selection, newline normalisation, and the hash -- to the tool being
    /// replaced, not just to itself.
    #[test]
    fn digest_agrees_with_the_python_original() {
        let corpus = "aabbcc\tpush-rbx\tpush rbx | .pushreg rbx\n\
                      ddeeff\talloc-small-8\tsub rsp, 8 | .allocstack 8\n";
        assert_eq!(
            corpus_digest(corpus),
            "dbde995121c6454b98c02db61ed9d72faeccd0c55111682a5da165d51b3b5b5d"
        );
    }

    #[test]
    fn blank_lines_are_skipped_and_short_rows_rejected() {
        let ok = "aa\tone\tpush rbx | .pushreg rbx\n\n   \nbb\ttwo\tpush rbp | .pushreg rbp\n";
        assert_eq!(parse_rows(ok).unwrap().len(), 2);

        let short = "aa\tone\n";
        assert_eq!(
            parse_rows(short).unwrap_err(),
            "malformed corpus row: 'aa\\tone'"
        );

        // Four fields is malformed too: an extra column means the generator and
        // this tool disagree about the format, which is not a thing to guess at.
        let long = "aa\tone\tpush rbx\textra\n";
        assert!(parse_rows(long).is_err());
    }

    #[test]
    fn preflight_reports_the_first_failure_only() {
        // A corpus that fails both the digest and the row count reports the
        // digest, because that is the order the checks run in.
        let wrong = "aa\tone\tpush rbx | .pushreg rbx\n";
        let message = preflight(wrong).unwrap_err();
        assert!(message.starts_with("corpus digest "), "{message}");
        assert!(message.contains(EXPECTED_DIGEST), "{message}");
    }

    #[test]
    fn epilogue_undoes_the_prologue_in_reverse() {
        assert_eq!(
            epilogue_for(&["push r12", "push r13", "sub rsp, 32"]),
            "    add rsp, 32\n    pop r13\n    pop r12"
        );
        // A frame-pointer establishing instruction has no inverse here, and is
        // dropped rather than guessed at.
        assert_eq!(epilogue_for(&["lea rbp, [rsp+32]"]), "");
    }

    #[test]
    fn masm_source_alternates_instructions_and_directives() {
        let src = masm_source("push rbx | .pushreg rbx | sub rsp, 32 | .allocstack 32");
        let expected = ".CODE\n\
                        grassprobe PROC FRAME\n\
                        \x20   push rbx\n\
                        \x20   .pushreg rbx\n\
                        \x20   sub rsp, 32\n\
                        \x20   .allocstack 32\n\
                        \x20   .endprolog\n\
                        \x20   xor eax, eax\n\
                        \x20   add rsp, 32\n\
                        \x20   pop rbx\n\
                        \x20   ret\n\
                        grassprobe ENDP\n\
                        END\n";
        assert_eq!(src, expected);
    }

    /// Which `ml64` gets picked when a machine has more than one Visual Studio
    /// is decided by this ordering, and the two plausible orderings disagree.
    /// `Program Files` is a prefix of `Program Files (x86)`, so component-wise
    /// it sorts first and the `(x86)` tree wins the "newest last" pick --
    /// the opposite of what flat string comparison would give.
    #[test]
    fn paths_order_by_component_the_way_pathlib_does() {
        let mut paths = [
            PathBuf::from("C:/Program Files/Microsoft Visual Studio/2022/Community/x/ml64.exe"),
            PathBuf::from(
                "C:/Program Files (x86)/Microsoft Visual Studio/18/BuildTools/x/ml64.exe",
            ),
        ];
        paths.sort_by_key(|p| path_sort_key(p.as_path()));
        assert!(
            paths.last().unwrap().to_string_lossy().contains("(x86)"),
            "{paths:?}"
        );

        // Within one tree the toolset version is compared as text, which is
        // what the Python original did and is wrong for a two-digit minor: see
        // the port report.
        let mut versions = [
            PathBuf::from("C:/vs/MSVC/14.9/ml64.exe"),
            PathBuf::from("C:/vs/MSVC/14.44/ml64.exe"),
        ];
        versions.sort_by_key(|p| path_sort_key(p.as_path()));
        assert!(versions.last().unwrap().to_string_lossy().contains("14.9"));
    }

    #[test]
    fn safe_name_keeps_only_what_a_file_system_will_take() {
        assert_eq!(safe_name("push-rbx"), "push-rbx");
        assert_eq!(safe_name("frame rbp/0"), "frame_rbp_0");
        assert_eq!(safe_name("a.b_c-1"), "a.b_c-1");
    }

    /// A minimal COFF object: a header claiming one section, a section header
    /// named `.xdata`, and its raw data. Built by hand so the reader can see
    /// which offsets this parser depends on.
    fn coff_with_xdata(name: &[u8; 8], payload: &[u8]) -> Vec<u8> {
        let mut data = vec![0u8; 20 + 40];
        data[2..4].copy_from_slice(&1u16.to_le_bytes()); // NumberOfSections
        data[16..18].copy_from_slice(&0u16.to_le_bytes()); // SizeOfOptionalHeader
        let off = 20;
        data[off..off + 8].copy_from_slice(name);
        let ptr = (20 + 40) as u32;
        data[off + 16..off + 20].copy_from_slice(&(payload.len() as u32).to_le_bytes());
        data[off + 20..off + 24].copy_from_slice(&ptr.to_le_bytes());
        data.extend_from_slice(payload);
        data
    }

    #[test]
    fn xdata_is_read_in_file_order() {
        let obj = coff_with_xdata(b".xdata\0\0", &[0x01, 0x0a, 0x04, 0x00]);
        assert_eq!(xdata_of(&obj).unwrap(), &[0x01, 0x0a, 0x04, 0x00]);
        // Not word-grouped, which is the mistake `dumpbin /rawdata` invites.
        assert_eq!(hex_of(xdata_of(&obj).unwrap()), "010a0400");
    }

    #[test]
    fn xdata_absent_or_truncated_is_none() {
        assert!(xdata_of(&[]).is_none());
        assert!(xdata_of(&coff_with_xdata(b".text\0\0\0", &[1, 2, 3])).is_none());

        // A section header pointing past the end of the file is refused rather
        // than read short: a truncated object must not look like a mismatch.
        let mut obj = coff_with_xdata(b".xdata\0\0", &[1, 2, 3, 4]);
        obj[20 + 16..20 + 20].copy_from_slice(&9999u32.to_le_bytes());
        assert!(xdata_of(&obj).is_none());
    }

    #[test]
    fn detail_is_one_line_and_bounded() {
        let detail = collapse_detail(b"first\r\nsecond\r\n", b"third\n");
        assert_eq!(detail, "first; second; third");
        let long = vec![b'x'; 500];
        assert_eq!(collapse_detail(&long, b"").len(), 300);
    }

    #[test]
    fn a_clean_run_reports_success_on_stdout_and_exits_zero() {
        let report = build_report(52, &[], &[]);
        assert_eq!(report.code, 0);
        assert_eq!(
            report.stdout,
            "win64 unwind differential: 52 prologues, .xdata byte-identical to ml64 on all of them\n"
        );
        assert!(report.stderr.is_empty());
    }

    #[test]
    fn a_mismatch_fails_and_names_both_sides() {
        let m = Mismatch {
            name: "push-rbx".into(),
            want: "0101010001300000".into(),
            got: "0101010001500000".into(),
            masm: "push rbx | .pushreg rbx".into(),
        };
        let report = build_report(52, std::slice::from_ref(&m), &[]);
        assert_eq!(report.code, 1);
        assert!(report.stdout.is_empty());
        assert!(report.stderr.contains("MISMATCH  push-rbx"));
        assert!(report.stderr.contains("    grass     0101010001300000"));
        assert!(report.stderr.contains("    ml64      0101010001500000"));
        assert!(report
            .stderr
            .contains("52 rows, 52 assembled, 1 disagree with ml64, 0 could not be assembled"));
    }

    /// A row the oracle could not assemble is a failure, not a skip. This is
    /// the decision the module docstring argues for, so it gets a test of its
    /// own rather than riding on the mismatch case.
    #[test]
    fn an_unassembled_row_fails_even_with_no_mismatches() {
        let errors = vec![(
            "frame-rbp-240".to_string(),
            "ml64 failed: A2008".to_string(),
        )];
        let report = build_report(52, &[], &errors);
        assert_eq!(report.code, 1);
        assert!(report
            .stderr
            .starts_with("ERROR  frame-rbp-240: ml64 failed: A2008\n"));
        assert!(report
            .stderr
            .contains("52 rows, 51 assembled, 0 disagree with ml64, 1 could not be assembled"));
    }
}
