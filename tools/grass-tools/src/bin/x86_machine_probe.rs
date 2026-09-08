//! Execute Grass's encoded instructions on the real processor and compare.
//!
//! `docs/VALIDATION.md` section 2 layer 3: "Physical probes: execute generated
//! instruction/API cases on named CPU/OS/GPU profiles and compare complete
//! declared effects."
//!
//! Every other check in this repository compares Grass against a document or
//! against another tool. This one compares it against silicon, and it is the
//! only layer that can settle a question the manuals leave ambiguous -- which
//! matters right now, because `Grass/ISA/X86/Sources.lean` records the AMD
//! manual as unretrievable and no citation anchor is confirmed.
//!
//! Hardware is a fallible oracle, not authority. `docs/VALIDATION.md` section 2:
//! "Tools and hardware are fallible oracles. Disagreement is preserved as a
//! finding; majority vote does not establish truth." A failing probe is a
//! finding against Grass, against this harness, or a genuine erratum, and is
//! resolved by reading the manual -- not by editing the model until it matches.
//!
//! ## How a probe runs
//!
//! NASM assembles a wrapper that loads a register file from a buffer, executes
//! the bytes under test, and stores the register file and RFLAGS back. Only the
//! bytes under test come from Grass; everything around them comes from NASM, so
//! a bug in Grass's encoder cannot also write its own scaffolding.
//!
//! RSP is never loaded from the buffer. It is the harness's own stack, and a
//! probe that redirected it would take the process with it.
//!
//! ## Isolation
//!
//! An instruction under test can fault, and `docs/VALIDATION.md` section 4
//! requires probe processes to be isolated when faults or hangs are possible.
//! Each probe runs in a child process, and the child installs a vectored
//! exception handler that terminates with the fault's own NTSTATUS the moment a
//! hardware fault arrives.
//!
//! That handler is not decoration. Without it every fault reported 0xC0000005:
//! the foreign call is wrapped in SEH, and the wrapper faults with nine unpopped
//! pushes and callee-saved registers full of test values, so unwinding dies on
//! the corrupted stack with a *second*, genuine access violation -- and that is
//! the code the parent saw. A reviewer measured UD2, HLT and INT3 all reporting
//! 0xC0000005, which made three entries of the status table unreachable. A
//! vectored handler runs before any unwinding, so the original code survives:
//! UD2 reports 0xC000001D, HLT 0xC0000096, INT3 0x80000003. The handler passes
//! anything outside the hardware-fault set through, so it cannot swallow the
//! runtime's own exception handling.
//!
//! That makes a faulting probe data rather than a crash, which is what the
//! fault-declaration facet of `docs/INSTRUCTIONS.md` section 3 will need.
//!
//! A timeout guards against a probe that does not return at all.
//!
//! ## Scope
//!
//! User mode only. Ring 0 instructions cannot be reached from a process and are
//! not attempted here; they need a bare-metal or hypervisor harness.
//!
//! Usage:
//!     lake env lean --run Tests/ISA/X86/MachineProbes.lean > probes.txt
//!     x86-machine-probe probes.txt
//!
//! Exit status is 1 if any probe disagrees with the model.
//!
//! ## About this port
//!
//! This replaces `Tools/x86-machine-probe.py`. The Python original spawned a
//! second Python interpreter as the isolated child and handed it a worker
//! script written to the temporary directory; this binary re-executes *itself*
//! with `--probe-worker`, which is the same isolation with one less artifact.
//! That flag is the only argument this tool accepts beyond the corpus path, and
//! it is not part of the interface a human uses.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// General-purpose registers in encoding order, which is the order the corpus,
/// the wrapper's buffer and this report all use.
const REGS: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];

/// Never loaded or compared: it is the harness's own stack.
const RSP: usize = 4;

/// The corpus this tool was last reviewed against. See `corpus_digest`.
const EXPECTED_DIGEST: &str = "2657182b0661e3e476e02c2111e5adac8beb3f43818d242da97e3834b75200c1";

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
const EXPECTED_ROWS: usize = 27;

const PROBE_TIMEOUT_SECONDS: u64 = 30;

/// The argument that puts this binary into its isolated-child role. Chosen to
/// be something no corpus path is, because it is checked before the
/// one-argument usage rule the human-facing interface follows.
const WORKER_FLAG: &str = "--probe-worker";

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
/// `win64_unwind_differential.rs`; the binaries are deliberately self-contained
/// so that a change to one cannot alter the other's verdict.
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

        // The padding loop above makes `msg` a whole number of 64-byte blocks, so
        // both remainders here are empty. `as_chunks` yields `&[u8; N]`, which
        // `from_be_bytes` takes directly, and zipping the sixteen words it
        // produces replaces the `take(16)` and the manual range indexing.
        let (blocks, _) = msg.as_chunks::<64>();
        for chunk in blocks {
            let mut w = [0u32; 64];
            let (bytes, _) = chunk.as_chunks::<4>();
            for (word, raw) in w.iter_mut().zip(bytes.iter()) {
                *word = u32::from_be_bytes(*raw);
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

/// Python's universal newlines, which `Path.read_text` applied before any of
/// this tool's parsing saw the corpus. A corpus written on Windows arrives with
/// `\r\n` and must hash the same as one written on Linux.
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
/// Python, each of which then fails the eight-field check. Matching means a
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

/// Python's `repr` of a string, for the malformed-line message. The quoting
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

/// A 64-bit hex field from the corpus or from a worker's reply.
fn parse_hex_u64(text: &str) -> Result<u64, String> {
    let t = text.trim();
    let digits = t
        .strip_prefix("0x")
        .or_else(|| t.strip_prefix("0X"))
        .unwrap_or(t);
    u64::from_str_radix(digits, 16)
        .map_err(|_| format!("not a 64-bit hex value: {}", python_repr(text)))
}

// ---------------------------------------------------------------------------
// Corpus
// ---------------------------------------------------------------------------

/// The probe's label, its register inputs, and the rule it checks. The encoded
/// bytes and the expected register outputs are what the processor judges.
fn coverage_of(line: &str) -> String {
    let fields: Vec<&str> = line.split('\t').collect();
    if fields.len() < 8 {
        return line.to_string();
    }
    [fields[0], fields[2], fields[4], fields[5], fields[6]].join("\t")
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

/// One corpus row: what to run, from what state, and what the model predicts.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ProbeRow {
    label: String,
    insn: String,
    /// Sixteen registers in encoding order, then the incoming RFLAGS: exactly
    /// the seventeen slots the wrapper's buffer has.
    before: Vec<u64>,
    /// The sixteen registers the model predicts.
    expected: Vec<u64>,
    /// `"exception"` for a prediction the general operand-size rule gets wrong,
    /// which the report separates out; anything else is an ordinary rule.
    kind: String,
    note: String,
    /// `None` where Grass does not model the flags, which is almost everywhere.
    /// The measured value is still reported; nothing is compared against it.
    flags_out: Option<u64>,
}

/// Parse the corpus, or the message explaining why it is not usable.
///
/// Blank lines are skipped; every other line must have exactly eight fields.
/// The register files must be sixteen wide, which the Python original assumed
/// rather than checked -- see the port report.
fn parse_rows(text: &str) -> Result<Vec<ProbeRow>, String> {
    let mut rows = Vec::new();
    for line in python_splitlines(text) {
        if line.trim().is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.split('\t').collect();
        if parts.len() != 8 {
            return Err(format!(
                "malformed probe line, expected 8 fields: {}",
                python_repr(line)
            ));
        }
        let (label, insn, before, after, kind, note, flags_in, flags_out) = (
            parts[0], parts[1], parts[2], parts[3], parts[4], parts[5], parts[6], parts[7],
        );
        let mut before_vals = Vec::with_capacity(17);
        for v in before.split(',') {
            before_vals.push(
                parse_hex_u64(v)
                    .map_err(|e| format!("{e} in the `before` column of {}", python_repr(line)))?,
            );
        }
        if before_vals.len() != 16 {
            return Err(format!(
                "the `before` column has {} registers, expected 16: {}",
                before_vals.len(),
                python_repr(line)
            ));
        }
        before_vals.push(
            parse_hex_u64(flags_in)
                .map_err(|e| format!("{e} in the `flags in` column of {}", python_repr(line)))?,
        );
        let mut expected = Vec::with_capacity(16);
        for v in after.split(',') {
            expected.push(
                parse_hex_u64(v)
                    .map_err(|e| format!("{e} in the `after` column of {}", python_repr(line)))?,
            );
        }
        if expected.len() != 16 {
            return Err(format!(
                "the `after` column has {} registers, expected 16: {}",
                expected.len(),
                python_repr(line)
            ));
        }
        rows.push(ProbeRow {
            label: label.to_string(),
            insn: insn.to_string(),
            before: before_vals,
            expected,
            kind: kind.to_string(),
            note: note.to_string(),
            flags_out: if flags_out == "-" {
                None
            } else {
                Some(parse_hex_u64(flags_out).map_err(|e| {
                    format!("{e} in the `flags out` column of {}", python_repr(line))
                })?)
            },
        });
    }
    Ok(rows)
}

/// The checks that must pass before a single instruction is executed, in the
/// order the Python original ran them: shape, then size, then digest. The order
/// is observable, because only the first failure is reported.
fn preflight(text: &str) -> Result<Vec<ProbeRow>, String> {
    let rows = parse_rows(text)?;
    if rows.len() < EXPECTED_ROWS {
        return Err(format!(
            "corpus has {} rows, fewer than the {EXPECTED_ROWS} this tool was \
             reviewed against. Coverage may only grow; if the reduction is \
             deliberate, lower EXPECTED_ROWS in the same reviewed edit that \
             shrinks the corpus.",
            rows.len()
        ));
    }
    let actual_digest = corpus_digest(text);
    if actual_digest != EXPECTED_DIGEST {
        return Err(format!(
            "corpus digest {actual_digest} does not match the reviewed \
             {EXPECTED_DIGEST}. Regenerate it from the Lean corpus, or update \
             EXPECTED_DIGEST here if the corpus genuinely changed."
        ));
    }
    Ok(rows)
}

// ---------------------------------------------------------------------------
// The wrapper NASM assembles around one instruction
// ---------------------------------------------------------------------------

/// The wrapper body, verbatim from the Python original including the stray
/// trailing comment line at the end of the RSP note, which is a leftover from
/// an edit and is preserved rather than tidied: this port is not the place to
/// change what NASM is handed.
const TEMPLATE: &str = r"; probe(buf in rcx). buf is 17 qwords: 16 GPRs in encoding order, then RFLAGS.
;
; Callee-saved state and the buffer pointer live in a save area inside this
; allocation, addressed RIP-relatively, not on the stack. The stack is exactly
; what a probe may move, and parking our own state there is why `push rax` used
; to be reported as a processor fault.
  ; Take the return address off the stack immediately. A probe that writes at
  ; [rsp] would otherwise overwrite it and `ret` would jump into whatever it
  ; wrote -- a harness limitation that would read as a processor fault.
  pop qword [rel save_ret]
  mov [rel save_rbx], rbx
  mov [rel save_rbp], rbp
  mov [rel save_rsi], rsi
  mov [rel save_rdi], rdi
  mov [rel save_r12], r12
  mov [rel save_r13], r13
  mov [rel save_r14], r14
  mov [rel save_r15], r15
  mov [rel save_rsp], rsp
  mov [rel save_buf], rcx

  mov rax, rcx
{loads}
  ; Incoming flags, from slot 16. A memory-operand push needs no scratch
  ; register, so this can happen after every register is loaded.
  push qword [rax+8*16]
  popfq
  mov rax, [rax+8*0]        ; mov does not modify flags

  db {body}

  ; `mov` does not modify flags, so the outgoing flags survive until the
  ; stack has been restored and pushfq is safe again.
  mov [rel save_rax], rax
  mov rsp, [rel save_rsp]
  pushfq
  pop rax
  mov [rel save_flags], rax
  mov rax, [rel save_buf]
{stores}
  mov rcx, [rel save_rax]
  mov [rax+8*0], rcx
  mov rcx, [rel save_flags]
  mov [rax+8*16], rcx
  ; Report the stack pointer as it was *before* the probe ran. `save_rsp` is
  ; written above and never rewritten, so this is the entry value, not the
  ; value the probe left behind -- and slot 4 is excluded from comparison
  ; anyway. A reviewer measured the difference against an in-probe capture and
  ; found it is exactly the negation of the probe's stack delta.
  ;
  ; So a probe that moves RSP is unobservable here, twice over. Reporting the
  ; value after the body -- which needs a second store below the epilogue's
  ; restore -- is an open obligation; the shipped corpus contains no
  ; stack-moving probe, so nothing currently depends on it.
  ; visible as data instead of corrupting the harness.
  mov rcx, [rel save_rsp]
  mov [rax+8*4], rcx

  mov rbx, [rel save_rbx]
  mov rbp, [rel save_rbp]
  mov rsi, [rel save_rsi]
  mov rdi, [rel save_rdi]
  mov r12, [rel save_r12]
  mov r13, [rel save_r13]
  mov r14, [rel save_r14]
  mov r15, [rel save_r15]
  jmp qword [rel save_ret]

align 16
save_rbx:   dq 0
save_rbp:   dq 0
save_rsi:   dq 0
save_rdi:   dq 0
save_r12:   dq 0
save_r13:   dq 0
save_r14:   dq 0
save_r15:   dq 0
save_rsp:   dq 0
save_buf:   dq 0
save_rax:   dq 0
save_flags: dq 0
save_ret:   dq 0
";

/// NASM source for the probe wrapper around one instruction.
///
/// The buffer is 17 qwords: sixteen GPRs in encoding order, then RFLAGS. Slot 4
/// is RSP: it is not loaded from the buffer, and on the way out it reports the
/// stack pointer as it stood before the probe body ran. It is not the value the
/// probe left behind: `save_rsp` is written before the body and never
/// rewritten, so a probe that moved the stack cannot be detected from it. The
/// slot is excluded from comparison, and closing this is an open obligation
/// recorded in `TEMPLATE`.
///
/// Callee-saved state, the buffer pointer and the return address live in a save
/// area inside this allocation, addressed RIP-relatively. None of it is on the
/// stack, because the stack is exactly what a probe may move: parking the
/// harness's own state there is why an ordinary `push rax` used to be reported
/// as a processor fault, and why a `mov [rsp], rax` overwrote the return
/// address and crashed the child.
///
/// Incoming flags come from slot 16, so the state before the instruction is
/// controlled rather than whatever the runtime happened to leave. Outgoing
/// flags survive the stack restore because `mov` does not modify flags.
fn wrapper_source(insn_hex: &str) -> String {
    let chars: Vec<char> = insn_hex.chars().collect();
    let body = chars
        .chunks(2)
        .map(|pair| format!("0x{}", pair.iter().collect::<String>()))
        .collect::<Vec<_>>()
        .join(", ");
    let loads = (0..16)
        .filter(|i| *i != 0 && *i != RSP)
        .map(|i| format!("  mov {}, [rax+8*{i}]", REGS[i]))
        .collect::<Vec<_>>()
        .join("\n");
    let stores = (1..16)
        .filter(|i| *i != RSP)
        .map(|i| format!("  mov [rax+8*{i}], {}", REGS[i]))
        .collect::<Vec<_>>()
        .join("\n");
    let filled = TEMPLATE
        .replace("{loads}", &loads)
        .replace("{body}", &body)
        .replace("{stores}", &stores);
    format!("BITS 64\n{filled}")
}

// ---------------------------------------------------------------------------
// Locating NASM
// ---------------------------------------------------------------------------

/// `shutil.which`, in the Windows shape the original relied on: the current
/// directory is searched first, and a bare name is tried with each `PATHEXT`
/// extension.
fn which(name: &str) -> Option<PathBuf> {
    let mut dirs: Vec<PathBuf> = vec![PathBuf::from(".")];
    if let Some(path) = std::env::var_os("PATH") {
        dirs.extend(std::env::split_paths(&path));
    }
    let files: Vec<String> = if cfg!(windows) {
        let pathext = std::env::var("PATHEXT")
            .unwrap_or_else(|_| ".COM;.EXE;.BAT;.CMD;.VBS;.JS;.WS;.MSC".to_string());
        let exts: Vec<String> = pathext
            .split(';')
            .filter(|e| !e.is_empty())
            .map(|e| e.to_string())
            .collect();
        let lower = name.to_lowercase();
        if exts.iter().any(|e| lower.ends_with(&e.to_lowercase())) {
            vec![name.to_string()]
        } else {
            exts.iter().map(|e| format!("{name}{e}")).collect()
        }
    } else {
        vec![name.to_string()]
    };
    for dir in dirs {
        for file in &files {
            let candidate = dir.join(file);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

/// NASM, on `PATH` or where its Windows installer puts it. A missing assembler
/// is fatal rather than a skip: the wrapper is what keeps a bug in Grass's
/// encoder from also writing its own scaffolding, so there is no degraded mode
/// worth running.
fn find_tool(name: &str) -> Result<String, String> {
    if let Some(found) = which(name) {
        return Ok(found.to_string_lossy().into_owned());
    }
    let mut candidates: Vec<PathBuf> = Vec::new();
    if let Some(home) = std::env::var_os("USERPROFILE") {
        candidates.push(
            PathBuf::from(home)
                .join("AppData/Local/bin/NASM")
                .join(format!("{name}.exe")),
        );
    }
    candidates.push(PathBuf::from(format!("C:/Program Files/NASM/{name}.exe")));
    for candidate in candidates {
        if candidate.exists() {
            return Ok(candidate.to_string_lossy().into_owned());
        }
    }
    Err(format!(
        "{name} not found on PATH or in the usual install locations"
    ))
}

// ---------------------------------------------------------------------------
// Running a child with a deadline
// ---------------------------------------------------------------------------

/// What a finished (or abandoned) child left behind.
struct Captured {
    /// The raw exit code, which on Windows carries the NTSTATUS of a crash.
    code: Option<i32>,
    stdout: String,
    stderr: String,
    timed_out: bool,
}

/// Run a child to completion, or kill it once `timeout` has passed.
///
/// The streams are drained on their own threads because a probe that writes
/// more than a pipe buffer while we are not reading would block instead of
/// being killed by the deadline, which is the failure the deadline exists to
/// catch.
fn run_captured(command: &mut Command, timeout: Option<Duration>) -> std::io::Result<Captured> {
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let mut out_pipe = child.stdout.take().expect("stdout was piped");
    let mut err_pipe = child.stderr.take().expect("stderr was piped");
    let out_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = out_pipe.read_to_end(&mut buf);
        buf
    });
    let err_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = err_pipe.read_to_end(&mut buf);
        buf
    });

    let deadline = timeout.map(|t| Instant::now() + t);
    let mut timed_out = false;
    let status = loop {
        match child.try_wait()? {
            Some(status) => break Some(status),
            None => {
                if let Some(deadline) = deadline {
                    if Instant::now() >= deadline {
                        let _ = child.kill();
                        let _ = child.wait();
                        timed_out = true;
                        break None;
                    }
                }
                std::thread::sleep(Duration::from_millis(2));
            }
        }
    };

    let stdout = out_reader.join().unwrap_or_default();
    let stderr = err_reader.join().unwrap_or_default();
    Ok(Captured {
        code: status.and_then(|s| s.code()),
        stdout: universal_newlines(&String::from_utf8_lossy(&stdout)),
        stderr: universal_newlines(&String::from_utf8_lossy(&stderr)),
        timed_out,
    })
}

/// The NTSTATUS values worth naming in a report. Deliberately the parent's
/// smaller list rather than the child's fault set: a code outside it is still
/// reported, just without a name.
const KNOWN_STATUS: [(u32, &str); 7] = [
    (0xC000001D, "STATUS_ILLEGAL_INSTRUCTION"),
    (0xC0000005, "STATUS_ACCESS_VIOLATION"),
    (0xC0000094, "STATUS_INTEGER_DIVIDE_BY_ZERO"),
    (0xC000008C, "STATUS_ARRAY_BOUNDS_EXCEEDED"),
    (0xC0000096, "STATUS_PRIVILEGED_INSTRUCTION"),
    (0x80000003, "STATUS_BREAKPOINT"),
    (0xC00000FD, "STATUS_STACK_OVERFLOW"),
];

/// The status line for a child that did not exit cleanly.
///
/// Windows reports a crashed child's NTSTATUS as its exit code, so the fault
/// class survives. Negative values are the same code sign-extended.
fn fault_status(code: i32) -> String {
    let code = code as u32;
    let name = KNOWN_STATUS
        .iter()
        .find(|(c, _)| *c == code)
        .map(|(_, n)| *n)
        .unwrap_or("");
    let detail = if name.is_empty() {
        format!("{code:#010x}")
    } else {
        format!("{code:#010x} ({name})")
    };
    format!("faulted {detail}")
}

/// Run one probe in a child process. Returns (status, register file).
fn run_probe(worker: &Path, binary: &Path, before: &[u64]) -> (String, Option<Vec<u64>>) {
    let regs = before
        .iter()
        .map(|v| format!("{v:016x}"))
        .collect::<Vec<_>>()
        .join(",");
    let mut command = Command::new(worker);
    command.arg(WORKER_FLAG).arg(binary).arg(&regs);
    let captured = match run_captured(
        &mut command,
        Some(Duration::from_secs(PROBE_TIMEOUT_SECONDS)),
    ) {
        Ok(c) => c,
        Err(e) => return (format!("probe worker could not be started: {e}"), None),
    };
    if captured.timed_out {
        return ("timeout".to_string(), None);
    }
    match captured.code {
        Some(0) => {}
        Some(code) => return (fault_status(code), None),
        // No exit code at all means the child was signalled, which Windows does
        // not do; treating it as a fault of unknown class keeps the run going.
        None => return ("faulted (no exit status)".to_string(), None),
    }
    let line = match captured.stdout.trim().lines().next_back() {
        Some(line) => line.to_string(),
        None => {
            return (
                "probe worker exited 0 without a register file".to_string(),
                None,
            )
        }
    };
    let mut values = Vec::with_capacity(17);
    for field in line.split(',') {
        match parse_hex_u64(field) {
            Ok(v) => values.push(v),
            Err(e) => {
                return (
                    format!("unreadable register file from the probe worker: {e}"),
                    None,
                )
            }
        }
    }
    if values.len() != 17 {
        return (
            format!("probe worker reported {} slots, expected 17", values.len()),
            None,
        );
    }
    ("ok".to_string(), Some(values))
}

// ---------------------------------------------------------------------------
// Comparison
// ---------------------------------------------------------------------------

/// Where the model and the processor differ.
///
/// RSP is skipped: the wrapper reports the value from before the body ran, so
/// the slot carries no information about the probe. Flags are compared only
/// where the model committed to a prediction -- Grass does not model flags yet,
/// and comparing against a value it never claimed would manufacture findings.
fn differences(
    expected: &[u64],
    actual: &[u64],
    flags_out: Option<u64>,
) -> Vec<(String, u64, u64)> {
    let mut out = Vec::new();
    for i in 0..16 {
        if i == RSP {
            continue;
        }
        if expected[i] != actual[i] {
            out.push((REGS[i].to_string(), expected[i], actual[i]));
        }
    }
    if let Some(want) = flags_out {
        if actual[16] != want {
            out.push(("rflags".to_string(), want, actual[16]));
        }
    }
    out
}

/// The one-line rendering of a set of differences.
fn describe_differences(differing: &[(String, u64, u64)]) -> String {
    differing
        .iter()
        .map(|(name, e, a)| format!("{name}: model {e:#018x}, cpu {a:#018x}"))
        .collect::<Vec<_>>()
        .join("; ")
}

/// A probe whose prediction the processor did not confirm, or which never
/// produced a register file at all.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Disagreement {
    label: String,
    insn: String,
    note: String,
    detail: String,
}

/// A probe that confirmed a documented exception to the general rule.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Confirmed {
    label: String,
    insn: String,
    note: String,
}

/// What the campaign produced, and the verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Report {
    stdout: String,
    code: i32,
}

/// Turn the campaign's findings into the report and the verdict.
///
/// A confirmed exception is not a failure: it is a probe whose model prediction
/// was right *and* whose rule is one the general operand-size rule would get
/// wrong, which is the case worth naming in the report. Only a disagreement
/// sets the exit status.
fn build_report(
    total: usize,
    agree: usize,
    exceptions: &[Confirmed],
    disagree: &[Disagreement],
) -> Report {
    let mut out = format!(
        "{total} probes: {agree} agree with the model, {} confirm a documented \
         exception, {} disagree\n",
        exceptions.len(),
        disagree.len()
    );
    for c in exceptions {
        out.push_str(&format!(
            "\n  exception confirmed on this processor: {}\n",
            c.label
        ));
        out.push_str(&format!("    bytes: {}\n", c.insn));
        out.push_str(&format!("    {}\n", c.note));
    }
    if !disagree.is_empty() {
        out.push_str(&format!("\n{} disagreement(s):\n\n", disagree.len()));
        for d in disagree {
            out.push_str(&format!("  {}\n", d.label));
            out.push_str(&format!("    bytes: {}\n", d.insn));
            out.push_str(&format!("    {}\n", d.detail));
            out.push_str(&format!("    note:  {}\n", d.note));
        }
        return Report {
            stdout: out,
            code: 1,
        };
    }
    out.push_str("\nno disagreement between the model and this processor\n");
    Report {
        stdout: out,
        code: 0,
    }
}

// ---------------------------------------------------------------------------
// Host identification
// ---------------------------------------------------------------------------

/// CPython's Windows release tables, so that the identification line reads the
/// same as the Python original's on the same machine. The lookup takes the
/// first entry whose version is at most the running one.
///
/// Only `os_line` reads these, and only its `#[cfg(windows)]` arm, so a
/// non-Windows build has nothing to name a build number with. They are compiled
/// under `test` as well so the boundary cases stay checked on every platform the
/// suite runs on: the lookup is ordinary portable arithmetic, and the reason it
/// is worth testing -- an off-by-one at 22000 renames Windows 10 to 11 in a
/// record `docs/VALIDATION.md` section 3 requires -- has nothing to do with the
/// host.
#[cfg(any(windows, test))]
const CLIENT_RELEASES: [((u32, u32, u32), &str); 11] = [
    ((10, 1, 0), "post11"),
    ((10, 0, 22000), "11"),
    ((6, 4, 0), "10"),
    ((6, 3, 0), "8.1"),
    ((6, 2, 0), "8"),
    ((6, 1, 0), "7"),
    ((6, 0, 0), "Vista"),
    ((5, 2, 3790), "XP64"),
    ((5, 2, 0), "XPMedia"),
    ((5, 1, 0), "XP"),
    ((5, 0, 0), "2000"),
];

/// The server half of the same tables, on the same terms as [`CLIENT_RELEASES`].
#[cfg(any(windows, test))]
const SERVER_RELEASES: [((u32, u32, u32), &str); 11] = [
    ((10, 1, 0), "post2025Server"),
    ((10, 0, 26100), "2025Server"),
    ((10, 0, 20348), "2022Server"),
    ((10, 0, 17763), "2019Server"),
    ((6, 4, 0), "2016Server"),
    ((6, 3, 0), "2012ServerR2"),
    ((6, 2, 0), "2012Server"),
    ((6, 1, 0), "2008ServerR2"),
    ((6, 0, 0), "2008Server"),
    ((5, 2, 0), "2003Server"),
    ((5, 0, 0), "2000Server"),
];

/// The release name for a build number, on the same terms as
/// [`CLIENT_RELEASES`].
#[cfg(any(windows, test))]
fn release_for(version: (u32, u32, u32), is_client: bool) -> &'static str {
    let table: &[((u32, u32, u32), &str)] = if is_client {
        &CLIENT_RELEASES
    } else {
        &SERVER_RELEASES
    };
    table
        .iter()
        .find(|(v, _)| *v <= version)
        .map(|(_, r)| *r)
        .unwrap_or("")
}

/// Identification `docs/VALIDATION.md` section 3 requires a campaign to record.
/// Microcode revision is not exposed to a user-mode process on Windows and is
/// reported as unknown rather than guessed.
fn describe_host() -> Vec<String> {
    let machine = std::env::var("PROCESSOR_ARCHITEW6432")
        .or_else(|_| std::env::var("PROCESSOR_ARCHITECTURE"))
        .unwrap_or_default();
    let mut lines = vec![
        format!("machine:   {machine}"),
        os_line(),
        // The Python original recorded its interpreter version here. The
        // identity that matters is the harness's, and claiming a Python version
        // from a Rust binary would be a fiction in a record whose whole purpose
        // is to say what was run.
        format!(
            "harness:   x86-machine-probe {} (rust)",
            env!("CARGO_PKG_VERSION")
        ),
        "microcode: unknown (not readable from user mode)".to_string(),
    ];
    match cpu_registry_lines() {
        Some(found) => lines.extend(found),
        None => lines.push("cpu:       unavailable".to_string()),
    }
    lines
}

#[cfg(windows)]
fn os_line() -> String {
    let (major, minor, build, is_client) = windows_version();
    format!(
        "os:        Windows {} ({major}.{minor}.{build})",
        release_for((major, minor, build), is_client)
    )
}

#[cfg(not(windows))]
fn os_line() -> String {
    format!("os:        {}", std::env::consts::OS)
}

/// The CPU description Windows records for processor 0. Read with `reg` rather
/// than a registry API so that the value in the report is one an operator can
/// reproduce from a shell.
fn cpu_registry_lines() -> Option<Vec<String>> {
    let mut command = Command::new("reg");
    command.args([
        "query",
        r"HKLM\HARDWARE\DESCRIPTION\System\CentralProcessor\0",
    ]);
    let captured = run_captured(&mut command, Some(Duration::from_secs(15))).ok()?;
    if captured.timed_out {
        return None;
    }
    let mut lines = Vec::new();
    for key in ["ProcessorNameString", "Identifier", "VendorIdentifier"] {
        for raw in captured.stdout.split('\n') {
            if raw.contains(key) {
                // `reg` separates its columns with four spaces; the value is
                // whatever follows the last of them.
                let value = raw.split("    ").last().unwrap_or("").trim();
                lines.push(format!("{:<10} {value}", key.to_lowercase()));
                break;
            }
        }
    }
    Some(lines)
}

/// The running Windows version, and whether this is a client SKU.
///
/// `RtlGetVersion` rather than `GetVersionEx` because the latter reports what
/// the application manifest claims compatibility with, and a probe campaign
/// that records a shimmed version number has recorded nothing.
#[cfg(windows)]
fn windows_version() -> (u32, u32, u32, bool) {
    // Every field is present because the layout is the contract, even though
    // only four of them are read.
    #[allow(dead_code)]
    #[repr(C)]
    struct OsVersionInfoExW {
        dw_os_version_info_size: u32,
        dw_major_version: u32,
        dw_minor_version: u32,
        dw_build_number: u32,
        dw_platform_id: u32,
        sz_csd_version: [u16; 128],
        w_service_pack_major: u16,
        w_service_pack_minor: u16,
        w_suite_mask: u16,
        w_product_type: u8,
        w_reserved: u8,
    }

    #[link(name = "ntdll")]
    extern "system" {
        fn RtlGetVersion(info: *mut OsVersionInfoExW) -> i32;
    }

    // SAFETY: `info` is a live, correctly-sized `RTL_OSVERSIONINFOEXW` whose
    // `dwOSVersionInfoSize` tells `RtlGetVersion` how much of it may be
    // written, which is the contract the function documents. It writes only
    // into that struct and cannot fail for a correctly-sized one.
    let info = unsafe {
        let mut info: OsVersionInfoExW = std::mem::zeroed();
        info.dw_os_version_info_size = std::mem::size_of::<OsVersionInfoExW>() as u32;
        RtlGetVersion(&mut info);
        info
    };
    // VER_NT_WORKSTATION is 1; anything else is a server or domain controller.
    (
        info.dw_major_version,
        info.dw_minor_version,
        info.dw_build_number,
        info.w_product_type == 1,
    )
}

// ---------------------------------------------------------------------------
// The isolated child
// ---------------------------------------------------------------------------

/// Hardware faults a probe can raise. Anything else -- a panic, a C++ throw
/// inside the runtime -- is passed through, so this handler cannot swallow the
/// runtime's own exception handling.
#[cfg(windows)]
const PROBE_FAULTS: [u32; 10] = [
    0xC0000005, 0xC000001D, 0xC0000094, 0xC0000096, 0xC000008C, 0xC0000090, 0xC0000091, 0xC0000093,
    0xC00000FD, 0x80000003,
];

#[cfg(windows)]
mod fault_isolation {
    use super::PROBE_FAULTS;
    use std::ffi::c_void;

    // The handler reads only `exception_code`; the rest of the record is
    // spelled out because its layout is what puts that field at offset 0.
    #[allow(dead_code)]
    #[repr(C)]
    pub struct ExceptionRecord {
        pub exception_code: u32,
        pub exception_flags: u32,
        pub exception_record: *mut ExceptionRecord,
        pub exception_address: *mut c_void,
        pub number_parameters: u32,
        pub exception_information: [usize; 15],
    }

    #[repr(C)]
    pub struct ExceptionPointers {
        pub exception_record: *mut ExceptionRecord,
        pub context_record: *mut c_void,
    }

    pub type VectoredHandler = unsafe extern "system" fn(*mut ExceptionPointers) -> i32;

    #[link(name = "kernel32")]
    extern "system" {
        fn AddVectoredExceptionHandler(first: u32, handler: VectoredHandler) -> *mut c_void;
        fn GetCurrentProcess() -> *mut c_void;
        fn TerminateProcess(process: *mut c_void, exit_code: u32) -> i32;
    }

    /// EXCEPTION_CONTINUE_SEARCH: let the next handler decide.
    const CONTINUE_SEARCH: i32 = 0;

    /// Terminate with the fault's own NTSTATUS, before any unwinding.
    ///
    /// The wrapper faults with unpopped pushes and callee-saved registers full
    /// of test values, so letting SEH unwind produces a second access violation
    /// that would be reported instead of this one. That is why the fault class
    /// has to be captured here and not from whatever the process eventually
    /// dies of.
    unsafe extern "system" fn veh(info: *mut ExceptionPointers) -> i32 {
        // SAFETY: the OS calls a vectored handler with a valid
        // `EXCEPTION_POINTERS` whose `ExceptionRecord` is a valid
        // `EXCEPTION_RECORD`. The null checks cost nothing and mean a
        // malformed dispatch declines the exception instead of faulting
        // recursively inside the handler. Only a `u32` is read, and
        // `TerminateProcess` is async-signal-safe in the sense that matters
        // here: it neither allocates nor unwinds.
        unsafe {
            if info.is_null() || (*info).exception_record.is_null() {
                return CONTINUE_SEARCH;
            }
            let code = (*(*info).exception_record).exception_code;
            if PROBE_FAULTS.contains(&code) {
                TerminateProcess(GetCurrentProcess(), code);
            }
            CONTINUE_SEARCH
        }
    }

    /// Install the handler ahead of every other one, including the runtime's
    /// own stack-overflow guard, so a probe's fault is reported as itself.
    pub fn install() -> Result<(), &'static str> {
        // SAFETY: `veh` is a `'static` function with the exact signature
        // `PVECTORED_EXCEPTION_HANDLER` requires, and the handle returned is
        // only tested against null -- the handler stays installed for the
        // lifetime of this process, which is one probe long.
        let handle = unsafe { AddVectoredExceptionHandler(1, veh) };
        if handle.is_null() {
            return Err("AddVectoredExceptionHandler failed");
        }
        Ok(())
    }
}

#[cfg(windows)]
mod probe_memory {
    use std::ffi::c_void;

    #[link(name = "kernel32")]
    extern "system" {
        fn VirtualAlloc(
            address: *mut c_void,
            size: usize,
            allocation_type: u32,
            protect: u32,
        ) -> *mut c_void;
    }

    const MEM_COMMIT_RESERVE: u32 = 0x3000;
    /// PAGE_EXECUTE_READWRITE. The page is writable and executable at once,
    /// which is what the Python original did and is preserved here: separating
    /// the two with `VirtualProtect` would be better hygiene but would add a
    /// failure mode the original does not have, and this port is not the place
    /// to change what the harness does to memory.
    const PAGE_EXECUTE_READWRITE: u32 = 0x40;

    /// Copy `code` into a fresh executable page and run it with `buf` in RCX.
    ///
    /// The page is deliberately never freed: this process exists to run one
    /// probe and then exit, and a probe that faults never reaches a free.
    pub fn execute(code: &[u8], buf: &mut [u64; 17]) -> Result<(), &'static str> {
        // SAFETY: a null `address` asks the OS to choose one, and `code.len()`
        // is nonzero for any real probe. The return value is checked before it
        // is used; nothing is assumed about where the page lands.
        let addr = unsafe {
            VirtualAlloc(
                std::ptr::null_mut(),
                code.len(),
                MEM_COMMIT_RESERVE,
                PAGE_EXECUTE_READWRITE,
            )
        };
        if addr.is_null() {
            return Err("VirtualAlloc failed");
        }
        // SAFETY: the allocation above is at least `code.len()` bytes (the OS
        // rounds up to a page), is writable, and cannot overlap `code`, which
        // lives in this process's heap.
        unsafe { std::ptr::copy_nonoverlapping(code.as_ptr(), addr as *mut u8, code.len()) };

        // SAFETY: three claims, each of which the wrapper NASM assembled is
        // built to satisfy, and none of which rests on the bytes under test:
        //
        //  * The page is executable and holds `code.len()` bytes starting at
        //    offset 0, which is where NASM's `-f bin` output begins. x86 keeps
        //    its instruction cache coherent with writes, so no flush is needed.
        //  * `extern "C"` on x86-64 Windows is the only calling convention
        //    there is, and it passes the first argument in RCX -- which is
        //    where `wrapper_source` expects the buffer. The wrapper saves and
        //    restores every callee-saved general-purpose register, takes the
        //    return address off the stack before the probe body runs so that a
        //    probe writing at `[rsp]` cannot redirect the return, and restores
        //    RSP from its own save area before returning.
        //  * `buf` is a live array of exactly the seventeen qwords the wrapper
        //    reads and writes, and is not aliased for the duration of the call.
        //
        // What this does *not* claim is that the bytes under test are safe:
        // they are attacker-grade by construction. That is why this runs in a
        // child process with a vectored handler installed, and why the caller
        // treats the child's exit code as data.
        unsafe {
            let entry = std::mem::transmute::<*mut c_void, unsafe extern "C" fn(*mut u64)>(addr);
            entry(buf.as_mut_ptr());
        }
        Ok(())
    }
}

/// The isolated child: install the handler, map the probe, run it, report the
/// register file. Anything that goes wrong here exits nonzero, which the parent
/// reads as a fault -- the same as the Python worker, whose failures were
/// uncaught exceptions.
#[cfg(windows)]
fn worker_main(binary: &str, regs: &str) -> i32 {
    if let Err(message) = fault_isolation::install() {
        eprintln!("{message}");
        return 1;
    }
    let code = match std::fs::read(binary) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("cannot read {binary}: {e}");
            return 1;
        }
    };
    let mut buf = [0u64; 17];
    for (i, field) in regs.split(',').enumerate() {
        if i >= buf.len() {
            eprintln!("more than 17 register slots were supplied");
            return 1;
        }
        match parse_hex_u64(field) {
            Ok(v) => buf[i] = v,
            Err(e) => {
                eprintln!("{e}");
                return 1;
            }
        }
    }
    if let Err(message) = probe_memory::execute(&code, &mut buf) {
        eprintln!("{message}");
        return 1;
    }
    println!(
        "{}",
        buf.iter()
            .map(|v| format!("{v:016x}"))
            .collect::<Vec<_>>()
            .join(",")
    );
    0
}

#[cfg(not(windows))]
fn worker_main(_binary: &str, _regs: &str) -> i32 {
    eprintln!(
        "the probe worker needs Windows: it maps an executable page with \
         VirtualAlloc and isolates faults with a vectored exception handler"
    );
    1
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

fn main() -> std::process::ExitCode {
    std::process::ExitCode::from(run() as u8)
}

fn run() -> i32 {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 4 && args[1] == WORKER_FLAG {
        return worker_main(&args[2], &args[3]);
    }
    if args.len() != 2 {
        eprintln!("usage: x86-machine-probe <probes.txt>");
        return 1;
    }

    // NASM is located before the corpus is read, so a machine that cannot run
    // the campaign at all says so before it says anything about the corpus.
    let nasm = match find_tool("nasm") {
        Ok(nasm) => nasm,
        Err(message) => {
            eprintln!("{message}");
            return 1;
        }
    };

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

    let worker = match std::env::current_exe() {
        Ok(exe) => exe,
        Err(e) => {
            eprintln!("cannot find this executable to re-run as a probe worker: {e}");
            return 1;
        }
    };

    println!("x86 physical probe campaign");
    for line in describe_host() {
        println!("  {line}");
    }
    println!();

    let tmp = match tempfile::TempDir::new() {
        Ok(t) => t,
        Err(e) => {
            eprintln!("could not create a working directory: {e}");
            return 1;
        }
    };
    let asm = tmp.path().join("probe.asm");
    let binary = tmp.path().join("probe.bin");

    let mut agree = 0usize;
    let mut exceptions: Vec<Confirmed> = Vec::new();
    let mut disagree: Vec<Disagreement> = Vec::new();

    for row in &rows {
        if let Err(e) = std::fs::write(&asm, wrapper_source(&row.insn).as_bytes()) {
            disagree.push(Disagreement {
                label: row.label.clone(),
                insn: row.insn.clone(),
                note: row.note.clone(),
                detail: format!("wrapper failed to assemble: could not write the source: {e}"),
            });
            continue;
        }
        let mut command = Command::new(&nasm);
        command
            .arg("-f")
            .arg("bin")
            .arg("-o")
            .arg(&binary)
            .arg(&asm);
        let built = match run_captured(&mut command, None) {
            Ok(c) => c,
            Err(e) => {
                disagree.push(Disagreement {
                    label: row.label.clone(),
                    insn: row.insn.clone(),
                    note: row.note.clone(),
                    detail: format!("wrapper failed to assemble: {e}"),
                });
                continue;
            }
        };
        if built.code != Some(0) {
            disagree.push(Disagreement {
                label: row.label.clone(),
                insn: row.insn.clone(),
                note: row.note.clone(),
                detail: format!("wrapper failed to assemble: {}", built.stderr.trim()),
            });
            continue;
        }

        let (status, actual) = run_probe(&worker, &binary, &row.before);
        let Some(actual) = actual else {
            disagree.push(Disagreement {
                label: row.label.clone(),
                insn: row.insn.clone(),
                note: row.note.clone(),
                detail: status,
            });
            continue;
        };
        let differing = differences(&row.expected, &actual, row.flags_out);
        if !differing.is_empty() {
            disagree.push(Disagreement {
                label: row.label.clone(),
                insn: row.insn.clone(),
                note: row.note.clone(),
                detail: describe_differences(&differing),
            });
        } else if row.kind == "exception" {
            exceptions.push(Confirmed {
                label: row.label.clone(),
                insn: row.insn.clone(),
                note: row.note.clone(),
            });
        } else {
            agree += 1;
        }
    }

    let report = build_report(rows.len(), agree, &exceptions, &disagree);
    print!("{}", report.stdout);
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
        assert_eq!(
            sha256::hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    /// One corpus row, in the shape `Tests/ISA/X86/MachineProbes.lean` emits.
    fn row_line(label: &str, insn: &str, after_rax: &str, kind: &str, flags_out: &str) -> String {
        let ones = ["ffffffffffffffff"; 16].join(",");
        let mut after: Vec<String> = vec!["ffffffffffffffff".to_string(); 16];
        after[0] = after_rax.to_string();
        format!(
            "{label}\t{insn}\t{ones}\t{}\t{kind}\tnote text\t0000000000000202\t{flags_out}",
            after.join(",")
        )
    }

    #[test]
    fn coverage_keeps_the_columns_that_say_what_is_exercised() {
        let line = "label\tb844332211\tbefore\tafter\trule\tnote\t202\t-";
        assert_eq!(coverage_of(line), "label\tbefore\trule\tnote\t202");
        // Short lines are hashed whole rather than silently losing columns.
        assert_eq!(coverage_of("short\tline"), "short\tline");
    }

    #[test]
    fn digest_ignores_the_encoded_bytes_and_the_predicted_registers() {
        let a = row_line("l", "b844332211", "0000000011223344", "rule", "-") + "\n";
        let b = row_line("l", "ffffffffff", "00000000deadbeef", "rule", "-") + "\n";
        assert_eq!(corpus_digest(&a), corpus_digest(&b));
    }

    #[test]
    fn digest_tracks_coverage_changes() {
        let full = row_line("one", "90", "1", "rule", "-")
            + "\n"
            + &row_line("two", "90", "1", "rule", "-")
            + "\n";
        let shrunk = row_line("one", "90", "1", "rule", "-") + "\n";
        // Dropping a row, and reclassifying one as an exception, both move it.
        let reclassified = row_line("one", "90", "1", "rule", "-")
            + "\n"
            + &row_line("two", "90", "1", "exception", "-")
            + "\n";
        assert_ne!(corpus_digest(&full), corpus_digest(&shrunk));
        assert_ne!(corpus_digest(&full), corpus_digest(&reclassified));
    }

    #[test]
    fn digest_is_line_ending_agnostic() {
        let unix = row_line("one", "90", "1", "rule", "-") + "\n";
        let dos = universal_newlines(&(row_line("one", "90", "1", "rule", "-") + "\r\n"));
        assert_eq!(corpus_digest(&unix), corpus_digest(&dos));
    }

    /// A digest computed by `hashlib.sha256` in the Python original, over a
    /// corpus small enough to write down. This pins the whole chain -- column
    /// selection, newline normalisation, and the hash -- to the tool being
    /// replaced, not just to itself.
    #[test]
    fn digest_agrees_with_the_python_original() {
        let ones = ["0000000000000001"; 16].join(",");
        let twos = ["0000000000000002"; 16].join(",");
        let corpus = format!("lab\tb8\t{ones}\t{twos}\trule\tnote here\t0000000000000202\t-\n");
        assert_eq!(
            corpus_digest(&corpus),
            "1a04e5f7a99090cd4e087bc7c03bc33f36ca6b697973957da796b29489034e72"
        );
    }

    #[test]
    fn blank_lines_are_skipped_and_short_rows_rejected() {
        let text = row_line("one", "90", "1", "rule", "-")
            + "\n\n  \n"
            + &row_line("two", "90", "2", "exception", "0000000000000203")
            + "\n";
        let rows = parse_rows(&text).unwrap();
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].flags_out, None);
        assert_eq!(rows[1].flags_out, Some(0x203));
        assert_eq!(rows[1].kind, "exception");
        // 16 registers plus the incoming flags: the seventeen slots the
        // wrapper's buffer has.
        assert_eq!(rows[0].before.len(), 17);
        assert_eq!(rows[0].before[16], 0x202);
        assert_eq!(rows[0].expected.len(), 16);

        let seven = "a\tb\tc\td\te\tf\tg";
        let err = parse_rows(seven).unwrap_err();
        assert_eq!(
            err,
            "malformed probe line, expected 8 fields: 'a\\tb\\tc\\td\\te\\tf\\tg'"
        );
    }

    /// A row whose register file is the wrong width is rejected rather than
    /// indexed past the end. The Python original indexed it, which is a crash
    /// where the corpus deserves a diagnosis.
    #[test]
    fn a_short_register_file_is_a_named_error() {
        let line = "lab\t90\t0000000000000001\t0000000000000002\trule\tn\t202\t-";
        let err = parse_rows(line).unwrap_err();
        assert!(
            err.starts_with("the `before` column has 1 registers"),
            "{err}"
        );
    }

    #[test]
    fn preflight_checks_size_before_content() {
        // A one-row corpus fails on the row count, not on the digest, because
        // that is the order the Python original ran the two guards in.
        let text = row_line("one", "90", "1", "rule", "-") + "\n";
        let message = preflight(&text).unwrap_err();
        assert!(message.starts_with("corpus has 1 rows"), "{message}");
        assert!(message.contains("Coverage may only grow"), "{message}");
    }

    #[test]
    fn wrapper_never_loads_or_stores_the_stack_pointer() {
        let src = wrapper_source("b844332211");
        assert!(src.starts_with("BITS 64\n"));
        assert!(src.contains("  db 0xb8, 0x44, 0x33, 0x22, 0x11\n"));
        // Slot 4 is RSP. It must not appear on either side of the buffer.
        assert!(!src.contains("[rax+8*4]\n"));
        assert!(!src.contains("mov rsp, [rax+"));
        assert!(!src.contains("mov [rax+8*4], rsp"));
        // RAX is loaded last, from the buffer pointer it was holding.
        assert!(!src.contains("mov rax, [rax+8*0]\n"));
        assert!(src.contains("  mov rax, [rax+8*0]        ; mov does not modify flags\n"));
        // Every other register is loaded and stored.
        for (i, name) in REGS.iter().enumerate() {
            if i == 0 || i == RSP {
                continue;
            }
            assert!(
                src.contains(&format!("  mov {name}, [rax+8*{i}]\n")),
                "{name}"
            );
            assert!(
                src.contains(&format!("  mov [rax+8*{i}], {name}\n")),
                "{name}"
            );
        }
        // The incoming flags come from slot 16, not from whatever was left.
        assert!(src.contains("  push qword [rax+8*16]\n  popfq\n"));
    }

    /// The wrapper is what a bug in Grass's encoder must not be able to write,
    /// so it has to be the same text the reviewed Python harness handed NASM --
    /// not merely text with the same properties. These digests were taken from
    /// `Tools/x86-machine-probe.py`'s own `wrapper_source` before it was
    /// replaced; a whitespace change here moves them.
    #[test]
    fn wrapper_is_byte_identical_to_the_reviewed_python_harness() {
        for (insn, digest, len) in [
            (
                "b844332211",
                "29677b2ebcaaf44188541a0afd7f14a69667e73ac41b777012f9e97a6c4b57ab",
                3326,
            ),
            (
                "90",
                "0a7e53f82451699647d358c14e70f1d4ba75f171a181712d07e477763bb157f4",
                3302,
            ),
            (
                "0fbcc1",
                "ac201ca1b10b0918a9c846bf6968c011e60d115cfb44c77b56db8494a9095acb",
                3314,
            ),
        ] {
            let source = wrapper_source(insn);
            assert_eq!(source.len(), len, "{insn}");
            assert_eq!(sha256::hex(source.as_bytes()), digest, "{insn}");
        }
    }

    #[test]
    fn wrapper_body_splits_the_hex_into_bytes() {
        assert!(wrapper_source("90").contains("  db 0x90\n"));
        assert!(wrapper_source("0fbcc1").contains("  db 0x0f, 0xbc, 0xc1\n"));
        // An odd-length encoding is passed through as NASM will see it, so a
        // corpus defect shows up as an assembler error rather than as silently
        // different bytes.
        assert!(wrapper_source("0fb").contains("  db 0x0f, 0xb\n"));
    }

    #[test]
    fn differences_skip_the_stack_pointer_slot() {
        let mut expected = vec![0u64; 16];
        let mut actual = vec![0u64; 17];
        actual[RSP] = 0xdead_beef;
        assert!(differences(&expected, &actual, None).is_empty());

        expected[1] = 5;
        let found = differences(&expected, &actual, None);
        assert_eq!(found, vec![("rcx".to_string(), 5, 0)]);
        assert_eq!(
            describe_differences(&found),
            "rcx: model 0x0000000000000005, cpu 0x0000000000000000"
        );
    }

    #[test]
    fn flags_are_compared_only_where_the_model_predicted_them() {
        let expected = vec![0u64; 16];
        let mut actual = vec![0u64; 17];
        actual[16] = 0x246;
        // Grass does not model flags for most probes; an unpredicted value is
        // measured and reported, never compared.
        assert!(differences(&expected, &actual, None).is_empty());
        assert_eq!(
            differences(&expected, &actual, Some(0x202)),
            vec![("rflags".to_string(), 0x202, 0x246)]
        );
        assert!(differences(&expected, &actual, Some(0x246)).is_empty());
    }

    #[test]
    fn fault_status_names_the_codes_worth_naming() {
        assert_eq!(
            fault_status(0xC000001Du32 as i32),
            "faulted 0xc000001d (STATUS_ILLEGAL_INSTRUCTION)"
        );
        assert_eq!(
            fault_status(0x80000003u32 as i32),
            "faulted 0x80000003 (STATUS_BREAKPOINT)"
        );
        // A code the parent has no name for is still reported, not swallowed.
        assert_eq!(fault_status(0xC0000090u32 as i32), "faulted 0xc0000090");
        // The child's own exit(1) path arrives here as an ordinary code.
        assert_eq!(fault_status(1), "faulted 0x00000001");
    }

    #[test]
    fn a_clean_campaign_exits_zero() {
        let report = build_report(27, 27, &[], &[]);
        assert_eq!(report.code, 0);
        assert_eq!(
            report.stdout,
            "27 probes: 27 agree with the model, 0 confirm a documented exception, 0 disagree\n\
             \nno disagreement between the model and this processor\n"
        );
    }

    /// A confirmed exception is a success. It is reported separately because it
    /// is the case the general operand-size rule would get wrong, not because
    /// anything is wrong with it.
    #[test]
    fn confirmed_exceptions_are_not_failures() {
        let confirmed = Confirmed {
            label: "0x90 (one-byte NOP, not xchg eax/eax)".into(),
            insn: "90".into(),
            note: "expects RAX unchanged".into(),
        };
        let report = build_report(27, 24, std::slice::from_ref(&confirmed), &[]);
        assert_eq!(report.code, 0);
        assert!(report.stdout.starts_with(
            "27 probes: 24 agree with the model, 1 confirm a documented exception, 0 disagree\n"
        ));
        assert!(report.stdout.contains(
            "\n  exception confirmed on this processor: 0x90 (one-byte NOP, not xchg eax/eax)\n    bytes: 90\n    expects RAX unchanged\n"
        ));
        assert!(report
            .stdout
            .ends_with("no disagreement between the model and this processor\n"));
    }

    #[test]
    fn a_disagreement_exits_one_and_shows_both_sides() {
        let d = Disagreement {
            label: "mov eax, 0x11223344".into(),
            insn: "b844332211".into(),
            note: "32-bit write: bits 63:32 must become zero".into(),
            detail: "rax: model 0x0000000011223344, cpu 0xffffffff11223344".into(),
        };
        let report = build_report(27, 26, &[], std::slice::from_ref(&d));
        assert_eq!(report.code, 1);
        assert!(report.stdout.contains("\n1 disagreement(s):\n\n"));
        assert!(report
            .stdout
            .contains("  mov eax, 0x11223344\n    bytes: b844332211\n"));
        assert!(report
            .stdout
            .contains("    rax: model 0x0000000011223344, cpu 0xffffffff11223344\n"));
        assert!(report
            .stdout
            .contains("    note:  32-bit write: bits 63:32 must become zero\n"));
    }

    /// A probe that faulted or hung is a disagreement, not a skip: the model
    /// predicted a register file and the processor did not produce one.
    #[test]
    fn a_fault_counts_against_the_model() {
        let d = Disagreement {
            label: "ud2".into(),
            insn: "0f0b".into(),
            note: "n".into(),
            detail: "faulted 0xc000001d (STATUS_ILLEGAL_INSTRUCTION)".into(),
        };
        assert_eq!(build_report(27, 26, &[], std::slice::from_ref(&d)).code, 1);
        let timeout = Disagreement {
            detail: "timeout".into(),
            ..d
        };
        assert_eq!(build_report(27, 26, &[], &[timeout]).code, 1);
    }

    #[test]
    fn release_lookup_matches_cpythons_table() {
        assert_eq!(release_for((10, 0, 26200), true), "11");
        assert_eq!(release_for((10, 0, 19045), true), "10");
        assert_eq!(release_for((10, 0, 22000), true), "11");
        assert_eq!(release_for((10, 0, 21999), true), "10");
        // The GitHub runners this campaign runs on are server SKUs, where the
        // same build number has a different name.
        assert_eq!(release_for((10, 0, 20348), false), "2022Server");
        assert_eq!(release_for((10, 0, 26100), false), "2025Server");
        assert_eq!(release_for((4, 0, 0), true), "");
    }

    #[test]
    fn hex_fields_are_read_the_way_python_read_them() {
        assert_eq!(parse_hex_u64("ffffffffffffffff").unwrap(), u64::MAX);
        assert_eq!(parse_hex_u64("0000000000000202").unwrap(), 0x202);
        assert_eq!(parse_hex_u64(" 202 ").unwrap(), 0x202);
        assert_eq!(parse_hex_u64("0x202").unwrap(), 0x202);
        assert!(parse_hex_u64("").is_err());
        assert!(parse_hex_u64("zz").is_err());
    }
}
