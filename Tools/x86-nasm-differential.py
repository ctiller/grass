#!/usr/bin/env python3
"""Differential check of the Grass x86-64 encoder against NASM.

`docs/VALIDATION.md` section 2 layer 2 asks for a comparison against independent
encoders and assemblers "where independent tools exist". NASM is one.

This matters more than it sounds. Every theorem in `Grass/ISA/X86/**` relates
Grass's own definitions to each other: the round-trip theorems prove that the
decoder recovers what the encoder wrote, which a model with two ModR/M fields
transposed satisfies perfectly while emitting instructions no processor will
execute. An external assembler is the only thing in the repository that can
notice.

NASM is a fallible oracle, not authority. `docs/VALIDATION.md` section 2:
"Tools and hardware are fallible oracles. Disagreement is preserved as a
finding; majority vote does not establish truth." A mismatch is a finding
against Grass *or* against NASM, and is resolved by reading the vendor manual.

Usage:
    lake env lean --run Tests/ISA/X86/NasmCorpus.lean > corpus.txt
    python Tools/x86-nasm-differential.py corpus.txt

Exit status is 1 on any mismatch.

Why the corpus uses a displacement of 0x11223344: Grass's encoder always emits a
32-bit displacement, while NASM emits the shortest form. For a displacement that
does not fit in a signed byte the two agree exactly and a byte comparison is
meaningful. With a small displacement NASM would legitimately choose disp8 and
the comparison would report a policy difference as a defect. That restriction is
a real limit on what this check covers, and it is stated rather than hidden: the
short-displacement forms are exercised by the decoder, not by this tool.
"""

import hashlib
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path



COVERAGE_LINE = chr(10)


def coverage_of(line: str) -> str:
    """The NASM source. The other column is the bytes Grass emitted."""
    fields = line.split(chr(9))
    return fields[1] if len(fields) > 1 else line


def corpus_digest(text: str) -> str:
    """A digest of the corpus's *coverage*, line endings normalised.

    Hashes the columns that say what is exercised and not the columns holding
    what Grass emitted. That distinction was missing and it mattered: a reviewer
    mutated `encodeMem`, and this tool's entire output was the digest error
    telling them to update the constant. Following it, the real check reported
    60 mismatches -- so the guard fired first on precisely the change it adds
    nothing to, and its own remedy was to silence it. That is the shape of the
    row-count weakness described below, one column over.

    Hashing coverage keeps what the guard is for. A corpus that drops rows,
    duplicates them, or swaps hard cases for easy ones still changes this
    digest; a corpus whose byte column changed because the encoder changed does
    not, and goes straight to the oracle that can judge it.
    """
    normalised = COVERAGE_LINE.join(
        coverage_of(line.rstrip("\r"))
        for line in text.splitlines() if line.strip())
    return hashlib.sha256(normalised.encode("utf-8")).hexdigest()


def find_nasm() -> str:
    found = shutil.which("nasm")
    if found:
        return found
    # NASM's Windows installer does not add itself to PATH.
    for candidate in (
        Path.home() / "AppData/Local/bin/NASM/nasm.exe",
        Path("C:/Program Files/NASM/nasm.exe"),
        Path("C:/Program Files (x86)/NASM/nasm.exe"),
    ):
        if candidate.exists():
            return str(candidate)
    sys.exit("nasm not found on PATH or in the usual install locations")


# A listing line is: line number, address, hex bytes, then the source. A long
# instruction wraps onto a continuation line carrying the same line number, with
# the first part ending in "-". Warning lines put asterisks in the byte column.
LISTING = re.compile(r"^\s*(\d+)\s+[0-9A-F]{8}\s+([0-9A-F]+-?)\s*(.*)$")

PROLOGUE = ["BITS 64", "DEFAULT ABS"]

# The corpus this tool was last reviewed against. See corpus_digest.
EXPECTED_DIGEST = "6cb8fbdf038d027991aff78e4c61ddf1a1e8bf067edfd00d505a45cb5e28a660"
# The coverage this tool was reviewed at. Shrinking the corpus must be a
# deliberate, reviewed edit rather than a side effect of regenerating it.
#
# The digest above detects a substituted corpus but not a smaller one: an author
# who shrinks the generator gets a digest mismatch, is told to update the
# constant, updates it, and the tool passes over the smaller corpus. A reviewer
# demonstrated it -- one `.take 1` plus a digest update turned 1085 encodings
# into 1 and still reported no disagreement. `docs/VALIDATION.md` section 7's
# ratchet is meant to prevent exactly that, and this is it applied to corpora.
EXPECTED_ROWS = 1117


# Disagreements that were investigated and found to be NASM canonicalising an
# address rather than Grass encoding it wrongly. `docs/VALIDATION.md` section 2
# requires disagreement to be "preserved as a finding", so these are listed with
# their evidence and reported every run rather than filtered out silently.
#
# Each entry needs the exact source line, both encodings, and a reason that
# says how the equivalence was established -- not an assertion that it is fine.
KNOWN_CANONICALISATIONS = {
    ("lea rax, [nosplit r12*1+0x11223344]", "4a8d042544332211", "498d842444332211"):
        "Grass encodes [r12*1+d] as a scaled index with no base (SIB index=100 "
        "with REX.X=1, base=101, mod=00). NASM emits the base form (SIB base=100 "
        "with REX.B=1, index=100 meaning none, mod=10) and does so even under "
        "`nosplit`, which suppresses the reg*2 -> reg+reg split but not this "
        "rewrite. Both are 8 bytes and denote the same address. Verified with "
        "ndisasm -b 64: 4A8D042544332211 and 498D842444332211 both disassemble "
        "to `lea rax,[r12+0x11223344]`.",
}


def assemble(nasm: str, sources: list[str]) -> dict[int, bytes] | None:
    """Assemble each source line, returning its bytes keyed by corpus index.

    A listing is used rather than the flat binary because instruction lengths
    are exactly what may disagree: walking Grass's own lengths through NASM's
    output desynchronises after the first difference and reports every later
    instruction as wrong. The listing gives NASM's own per-line boundaries, so a
    length disagreement stays local and is reported as itself.
    """
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp) / "corpus.asm"
        lst = Path(tmp) / "corpus.lst"
        out = Path(tmp) / "corpus.bin"
        src.write_text("\n".join(PROLOGUE + sources) + "\n", encoding="ascii")
        result = subprocess.run(
            [nasm, "-f", "bin", "-l", str(lst), "-o", str(out), str(src)],
            capture_output=True, text=True,
        )
        if result.returncode != 0:
            print(result.stderr.strip(), file=sys.stderr)
            return None

        by_line: dict[int, str] = {}
        for raw in lst.read_text(encoding="utf-8", errors="replace").splitlines():
            match = LISTING.match(raw.replace("\r", ""))
            if not match:
                continue
            lineno, chunk, _ = match.groups()
            by_line[int(lineno)] = by_line.get(int(lineno), "") + chunk.rstrip("-")

        # Listing line numbers are 1-based and include the prologue.
        return {
            lineno - 1 - len(PROLOGUE): bytes.fromhex(hexed)
            for lineno, hexed in by_line.items()
            if lineno > len(PROLOGUE)
        }


def main() -> int:
    if len(sys.argv) != 2:
        sys.exit("usage: x86-nasm-differential.py <corpus.txt>")
    nasm = find_nasm()

    rows = []
    for line in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        hexbytes, source = line.split("\t", 1)
        rows.append((bytes.fromhex(hexbytes), source))

    if not rows:
        sys.exit("corpus is empty; did the Lean generator run?")
    if len(rows) < EXPECTED_ROWS:
        sys.exit(
            f"corpus has {len(rows)} rows, fewer than the {EXPECTED_ROWS} this "
            "tool was reviewed against. Coverage may only grow; if the "
            "reduction is deliberate, lower EXPECTED_ROWS in the same reviewed "
            "edit that shrinks the corpus.")

    actual_digest = corpus_digest(
        Path(sys.argv[1]).read_text(encoding="utf-8"))
    if actual_digest != EXPECTED_DIGEST:
        sys.exit(
            f"corpus digest {actual_digest} does not match the reviewed "
            f"{EXPECTED_DIGEST}. Regenerate it from the Lean corpus, or update "
            "EXPECTED_DIGEST here if the corpus genuinely changed."
        )

    assembled = assemble(nasm, [source for _, source in rows])
    if assembled is None:
        return 1

    mismatches = []
    canonicalisations = []
    for index, (expected, source) in enumerate(rows):
        actual = assembled.get(index)
        if actual is None:
            mismatches.append((source, expected.hex(), "<no bytes in listing>"))
        elif actual != expected:
            key = (source, expected.hex(), actual.hex())
            if key in KNOWN_CANONICALISATIONS:
                canonicalisations.append(key)
            else:
                mismatches.append(key)

    identical = len(rows) - len(mismatches) - len(canonicalisations)
    print(f"x86 NASM differential: {len(rows)} encodings, "
          f"{identical} byte-identical, "
          f"{len(canonicalisations)} known canonicalisation(s), "
          f"{len(mismatches)} unexplained")

    for source, grass_hex, nasm_hex in canonicalisations:
        print(f"\n  canonicalisation: {source}")
        print(f"    grass: {grass_hex}")
        print(f"    nasm : {nasm_hex}")
        print(f"    {KNOWN_CANONICALISATIONS[(source, grass_hex, nasm_hex)]}")

    if mismatches:
        print(f"\n{len(mismatches)} mismatch(es):\n")
        for source, expected, actual in mismatches[:40]:
            print(f"  {source}")
            print(f"    grass: {expected}")
            print(f"    nasm : {actual}")
        if len(mismatches) > 40:
            print(f"  ... and {len(mismatches) - 40} more")
        return 1

    print("no disagreement")
    return 0


if __name__ == "__main__":
    sys.exit(main())
