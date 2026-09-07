#!/usr/bin/env python3
"""Differential check of the Grass x86-64 decoder's instruction lengths against NDISASM.

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
    python Tools/x86-decode-differential.py decode.txt

Exit status is 1 on any length disagreement, and on a missing NDISASM: a
differential that passes because its oracle is absent is worse than none.

NDISASM is a fallible oracle, not authority. `docs/VALIDATION.md` section 2:
"Tools and hardware are fallible oracles. Disagreement is preserved as a
finding; majority vote does not establish truth."
"""

import hashlib
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# The corpus this tool was reviewed against, as a digest of its content. A row
# count is not enough: a truncated or duplicated corpus keeps a plausible count
# and checks nothing. See the same guard in the other x86 differentials.
EXPECTED_DIGEST = "41027a1384e283d2ae989569b9ee4f4ce105ac9376c48feff7ec8fcee29bd15e"
# The coverage this tool was reviewed at. Shrinking the corpus must be a
# deliberate, reviewed edit rather than a side effect of regenerating it.
#
# The digest above detects a substituted corpus but not a smaller one: an author
# who shrinks the generator gets a digest mismatch, is told to update the
# constant, updates it, and the tool passes over the smaller corpus. A reviewer
# demonstrated it -- one `.take 1` plus a digest update turned 1085 encodings
# into 1 and still reported no disagreement. `docs/VALIDATION.md` section 7's
# ratchet is meant to prevent exactly that, and this is it applied to corpora.
# The coverage this tool was reviewed at, as structural buckets rather than a
# row count.
#
# The row count was a proxy the author controls. A reviewer replaced the corpus
# with N copies of one row, updated the digest exactly as the error message
# instructs, and this tool reported full agreement over a corpus that exercised
# one case -- a result that read *better* than baseline. Counting distinct
# inputs instead means duplicating a row moves nothing, so the substitution is
# caught whether or not the digest is refreshed.
#
# Every bucket is a minimum. Raising coverage is free; lowering it is a reviewed
# edit, which is what `docs/VALIDATION.md` section 7's ratchet asks for.
EXPECTED_COVERAGE = {
    "distinct windows": 57440,
    "opcode rows": 38,
    "rex prefixes": 4,
    "modrm bytes": 256,
    "sib bytes": 256,
}


def coverage_buckets(rows):
    """What the corpus exercises, from each window's label.

    The label names the opcode row, the prefix and the operand bytes, which is
    the input; the window bytes and the reported length are under test.
    """
    labels = {label for _, _, label in rows}
    rows_seen, rex, modrm, sib = set(), set(), set(), set()
    for label in labels:
        parts = label.split("|")
        if parts:
            rows_seen.add(parts[0])
        for p in parts[1:]:
            if p.startswith("rex") or p == "norex":
                rex.add(p)
            elif p.startswith("modrm"):
                modrm.add(p)
            elif p.startswith("sib"):
                sib.add(p)
    return {
        "distinct windows": len(labels),
        "opcode rows": len(rows_seen),
        "rex prefixes": len(rex),
        "modrm bytes": len(modrm),
        "sib bytes": len(sib),
    }


def coverage_shortfall(rows):
    """Buckets that fall below their reviewed minimum, as (name, have, want)."""
    have = coverage_buckets(rows)
    return [(name, have.get(name, 0), want)
            for name, want in sorted(EXPECTED_COVERAGE.items())
            if have.get(name, 0) < want]


# Must match `Grass.Tests.ISA.X86.DecodeC.windowBytes`. The tool checks this
# against the corpus rather than trusting it.
WINDOW_BYTES = 24

LINE = re.compile(r"^([0-9A-Fa-f]{8})\s+([0-9A-Fa-f]+)\s+(\S.*)$")

# NDISASM's two ways of saying "these bytes are not an instruction".
#
# `db 0x..` is the obvious one. The other is subtler and accounts for three
# quarters of the cases here: given a REX prefix followed by bytes that do not
# form a legal instruction, NDISASM emits the prefix on a line of its own and
# resumes after it. `48 8D C0` -- LEA with `mod=11`, which is #UD because LEA
# has no register-source form -- prints as `rex.w` and then `db 0x8d`. Reading
# that first line as an instruction boundary would report a length of 1 and
# call it a disagreement, when what NDISASM actually said is that it refused.
PREFIX_ONLY = re.compile(r"rex(\.[wrxb]+)?$|^(o16|o32|a16|a32)$", re.IGNORECASE)


def is_refusal(text: str) -> bool:
    """Whether NDISASM declined to read an instruction at this offset."""
    return text.startswith("db ") or bool(PREFIX_ONLY.fullmatch(text))


COVERAGE_LINE = chr(10)


def coverage_of(line: str) -> str:
    """The window's label, which names the opcode, prefix and operand bytes.

    Split on "|" rather than "/": mnemonics contain slashes ("mov r/m, r"), so
    a slash-separated label could not be parsed unambiguously, and the mnemonic
    alone did not identify a row -- `plusRegRows` gives eight opcodes one
    mnemonic. Both were found by the coverage ratchet counting fewer distinct
    labels than there were windows."""
    fields = line.split(chr(9))
    return fields[2] if len(fields) > 2 else line


def corpus_digest(text: str) -> str:
    """A digest of the corpus's *coverage*, line endings normalised.

    Hashes the columns that say what is exercised and not the columns holding
    what Grass emitted. That distinction was missing and it mattered: a reviewer
    mutated `encodeMem`, and this tool's entire output was the digest error
    telling them to update the constant. Following it, the real check reported
    60 mismatches -- so the guard fired first on precisely the change it adds
    nothing to, and its own remedy was to silence it. That is the shape of the
    row-count weakness described below, one column over.

    Sorted, because coverage is a set and not a sequence. Reordering the
    generator's own enumeration -- swapping two entries in `Gpr.all`, say --
    leaves exactly the same cases exercised, and a digest that fired on it
    would route a real model change to the "update the constant" path instead
    of to the oracle. A reviewer raised that as the residue of the previous
    fix.

    Hashing coverage keeps what the guard is for. A corpus that drops rows,
    duplicates them, or swaps hard cases for easy ones still changes this
    digest; a corpus whose byte column changed because the encoder changed does
    not, and goes straight to the oracle that can judge it.
    """
    normalised = COVERAGE_LINE.join(
        sorted(coverage_of(line.rstrip("\r"))
               for line in text.splitlines() if line.strip()))
    return hashlib.sha256(normalised.encode("utf-8")).hexdigest()


def find_tool(name: str) -> str | None:
    found = shutil.which(name)
    if found:
        return found
    for candidate in (
        Path.home() / f"AppData/Local/bin/NASM/{name}.exe",
        Path(f"C:/Program Files/NASM/{name}.exe"),
    ):
        if candidate.exists():
            return str(candidate)
    return None


def disassemble_blob(ndisasm: str, blob: bytes) -> tuple[dict[int, str], list[int]]:
    """Disassemble the whole corpus in one pass.

    One invocation rather than one per row: 57k separate processes would take
    hours, and NDISASM decodes a flat blob continuously, which is exactly what
    is wanted here -- the boundaries it chooses *are* the lengths being checked.

    Returns the text at each instruction start and the sorted list of starts.
    """
    with tempfile.TemporaryDirectory() as tmp:
        binary = Path(tmp) / "corpus.bin"
        binary.write_bytes(blob)
        proc = subprocess.run(
            [ndisasm, "-b", "64", str(binary)],
            capture_output=True, text=True)
    if proc.returncode != 0:
        raise SystemExit(f"ndisasm failed: {proc.stderr.strip()[:300]}")
    text_at: dict[int, str] = {}
    for line in proc.stdout.splitlines():
        m = LINE.match(line)
        if not m:
            # Continuation lines for long encodings carry no address.
            continue
        text_at[int(m.group(1), 16)] = m.group(3).strip()
    return text_at, sorted(text_at)


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    text = Path(sys.argv[1]).read_text(encoding="utf-8")

    actual = corpus_digest(text)
    if actual != EXPECTED_DIGEST:
        print(
            f"corpus digest {actual} does not match the reviewed "
            f"{EXPECTED_DIGEST}. Regenerate it from the Lean corpus, or update "
            "EXPECTED_DIGEST here if the corpus genuinely changed.",
            file=sys.stderr)
        return 1

    rows = []
    for line in text.splitlines():
        if not line.strip():
            continue
        fields = line.rstrip("\r").split("\t")
        if len(fields) != 3:
            print(f"malformed corpus row: {line!r}", file=sys.stderr)
            return 1
        raw = bytes.fromhex(fields[0])
        if len(raw) != WINDOW_BYTES:
            print(
                f"row {fields[2]} is {len(raw)} bytes, expected {WINDOW_BYTES}; "
                "the corpus and this tool disagree about the window size",
                file=sys.stderr)
            return 1
        rows.append((raw, int(fields[1]), fields[2]))
    if not rows:
        print("corpus is empty", file=sys.stderr)
        return 1
    shortfall = coverage_shortfall(rows)
    if shortfall:
        print("corpus coverage fell below the reviewed minimums:",
              file=sys.stderr)
        for name, have, want in shortfall:
            print(f"    {name}: {have}, expected at least {want}",
                  file=sys.stderr)
        print(
            "Coverage may only grow, and duplicating rows does not raise it; "
            "if a reduction is deliberate, lower EXPECTED_COVERAGE in the same "
            "reviewed edit that shrinks the corpus.", file=sys.stderr)
        return 1

    ndisasm = find_tool("ndisasm")
    if ndisasm is None:
        print(
            "ndisasm not found on PATH or in the usual install locations. This "
            "is a failure rather than a skip: a differential check that passes "
            "because its oracle is absent is worse than no check.",
            file=sys.stderr)
        return 1

    blob = b"".join(r[0] for r in rows)
    text_at, starts = disassemble_blob(ndisasm, blob)
    start_set = set(starts)

    disagreements = []
    refused = 0
    unaligned = 0
    for index, (raw, grass_len, label) in enumerate(rows):
        base = index * WINDOW_BYTES
        if base not in start_set:
            # NDISASM's boundaries drifted into this window, which means the
            # previous instruction overran it. Reported rather than skipped.
            unaligned += 1
            continue
        if is_refusal(text_at[base]):
            refused += 1
            continue
        following = [s for s in (base + k for k in range(1, WINDOW_BYTES + 1))
                     if s in start_set]
        if not following:
            unaligned += 1
            continue
        oracle_len = following[0] - base
        if oracle_len != grass_len:
            disagreements.append(
                (label, raw[:max(grass_len, oracle_len)].hex(), grass_len,
                 oracle_len, text_at[base]))

    for label, hexbytes, grass, oracle, asm in disagreements[:40]:
        print(f"LENGTH  {label}", file=sys.stderr)
        print(f"    bytes    {hexbytes}", file=sys.stderr)
        print(f"    grass    {grass}", file=sys.stderr)
        print(f"    ndisasm  {oracle}  ({asm})", file=sys.stderr)
    if len(disagreements) > 40:
        print(f"    ... and {len(disagreements) - 40} more", file=sys.stderr)

    checked = len(rows) - refused - unaligned
    if disagreements or unaligned:
        print(
            f"x86 decode differential: {len(rows)} windows, {checked} compared, "
            f"{len(disagreements)} length disagreements, {refused} refused by "
            f"ndisasm as invalid encodings, {unaligned} unaligned",
            file=sys.stderr)
        return 1

    print(
        f"x86 decode differential: {len(rows)} windows, {checked} compared, "
        f"lengths agree with ndisasm on all of them; {refused} further windows "
        "are encodings ndisasm rejects as invalid, which this decoder accepts "
        "by design and which are not compared")
    return 0


if __name__ == "__main__":
    sys.exit(main())
