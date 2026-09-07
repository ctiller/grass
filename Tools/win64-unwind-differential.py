#!/usr/bin/env python3
"""Differential check of Grass's Win64 unwind metadata against MASM.

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
    lake env lean --run Tests/Emit.lean unwind > corpus.txt
    python Tools/win64-unwind-differential.py corpus.txt

Exit status is 1 on any mismatch, and also on an oracle that could not be run:
a check that silently passes because the assembler was missing is worse than no
check, so a missing `ml64.exe` is a failure rather than a skip.

`.xdata` is read out of the COFF object directly rather than through
`dumpbin /rawdata`, because `dumpbin` prints raw data grouped into little-endian
words -- with the default grouping the bytes come back in an order that is not
the file order, which is a good way to confirm a byte layout that is in fact
reversed.
"""

import hashlib
import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

# The corpus this tool was reviewed against, as a digest of its content.
#
# A row count is not enough: a corpus of one row, or one whose every row is a
# copy of the first, has a plausible count and checks nothing. Binding content
# means substituting a same-length corpus fails. Changing the corpus requires
# updating this constant, which is the reviewed edit `docs/VALIDATION.md`
# section 7 asks for rather than a silent change to what is being checked.
EXPECTED_DIGEST = "daae6c7fb5bb9a4bc600d380b86618708e61804b7c46ade83debcbdabe00f509"
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
    "distinct prologues": 95,
    "directives": 5,
    "registers pushed": 8,
    "allocation sizes": 40,
}


def coverage_buckets(rows):
    """What the corpus exercises, from each row's name and MASM text."""
    prologues = {masm for _, _, masm in rows}
    directives, pushed, allocs = set(), set(), set()
    for masm in prologues:
        for part in (p.strip() for p in masm.split("|")):
            if part.startswith("."):
                directives.add(part.split()[0])
            if part.startswith("push "):
                pushed.add(part.split()[1])
            if part.startswith("sub rsp, "):
                allocs.add(part.split(", ")[1])
    return {
        "distinct prologues": len(prologues),
        "directives": len(directives),
        "registers pushed": len(pushed),
        "allocation sizes": len(allocs),
    }


def coverage_shortfall(rows):
    """Buckets that fall below their reviewed minimum, as (name, have, want)."""
    have = coverage_buckets(rows)
    return [(name, have.get(name, 0), want)
            for name, want in sorted(EXPECTED_COVERAGE.items())
            if have.get(name, 0) < want]


TEMPLATE = """\
.CODE
grassprobe PROC FRAME
{prologue}
    .endprolog
    xor eax, eax
{epilogue}
    ret
grassprobe ENDP
END
"""


COVERAGE_LINE = chr(10)


def coverage_of(line: str) -> str:
    """The prologue's name and its MASM text. The first column is the .xdata
    Grass predicted."""
    fields = line.split(chr(9))
    return chr(9).join(fields[1:]) if len(fields) > 1 else line


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
    """Locate an MSVC tool, preferring an explicit environment override.

    MSVC is not on `PATH` unless a developer prompt set it up, so a plain
    `shutil.which` finds nothing on an otherwise perfectly capable machine.
    """
    override = os.environ.get(name.upper().replace(".EXE", "") + "_PATH")
    if override and Path(override).is_file():
        return override
    roots = [
        Path("C:/Program Files/Microsoft Visual Studio"),
        Path("C:/Program Files (x86)/Microsoft Visual Studio"),
    ]
    found = []
    for root in roots:
        if root.is_dir():
            found.extend(root.glob(f"*/*/VC/Tools/MSVC/*/bin/Hostx64/x64/{name}"))
    if not found:
        return None
    # Highest MSVC version last in sorted order; prefer the newest.
    return str(sorted(found)[-1])


def epilogue_for(steps: list[str]) -> str:
    """Undo the prologue, so the emitted procedure is not obvious nonsense.

    `ml64` builds `UNWIND_INFO` from the directives and does not check the
    epilogue, so this affects nothing that is being measured. It is here so the
    corpus does not depend on that being true.
    """
    out = []
    for text in reversed(steps):
        if text.startswith("push "):
            out.append("    pop " + text[len("push "):])
        elif text.startswith("sub rsp, "):
            out.append("    add rsp, " + text[len("sub rsp, "):])
    return "\n".join(out)


def xdata_of(obj: Path) -> bytes | None:
    """Read the `.xdata` section's raw bytes out of a COFF object."""
    data = obj.read_bytes()
    if len(data) < 20:
        return None
    n_sections, = struct.unpack_from("<H", data, 2)
    opt_size, = struct.unpack_from("<H", data, 16)
    base = 20 + opt_size
    for i in range(n_sections):
        off = base + i * 40
        if off + 40 > len(data):
            return None
        name = data[off:off + 8].rstrip(b"\0").decode("latin-1")
        if name != ".xdata":
            continue
        size, ptr = struct.unpack_from("<II", data, off + 16)
        if ptr == 0 or ptr + size > len(data):
            return None
        return data[ptr:ptr + size]
    return None


def assemble(ml64: str, workdir: Path, name: str, masm: str) -> tuple[bytes | None, str]:
    """Assemble one prologue and return its `.xdata` bytes."""
    parts = [p.strip() for p in masm.split("|")]
    instructions = [p for p in parts if not p.startswith(".")]
    prologue = "\n".join("    " + p for p in parts)
    source = TEMPLATE.format(
        prologue=prologue, epilogue=epilogue_for(instructions))
    asm = workdir / f"{name}.asm"
    obj = workdir / f"{name}.obj"
    asm.write_text(source, encoding="ascii")
    proc = subprocess.run(
        [ml64, "/nologo", "/c", "/Fo", str(obj), str(asm)],
        capture_output=True, text=True, cwd=str(workdir))
    if proc.returncode != 0:
        detail = (proc.stdout + proc.stderr).strip().replace("\n", "; ")
        return None, f"ml64 failed: {detail[:300]}"
    if not obj.is_file():
        return None, "ml64 produced no object"
    got = xdata_of(obj)
    if got is None:
        return None, "no .xdata section in the object"
    return got, ""


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    text = Path(sys.argv[1]).read_text(encoding="utf-8")

    actual_digest = corpus_digest(text)
    if actual_digest != EXPECTED_DIGEST:
        print(
            f"corpus digest {actual_digest} does not match the reviewed "
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
        rows.append(tuple(fields))
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

    ml64 = find_tool("ml64.exe")
    if ml64 is None:
        print(
            "ml64.exe not found. Set ML64_PATH, or install the MSVC build "
            "tools. This is a failure rather than a skip: a differential check "
            "that passes because its oracle is absent is worse than none.",
            file=sys.stderr)
        return 1

    mismatches = []
    errors = []
    with tempfile.TemporaryDirectory() as tmp:
        workdir = Path(tmp)
        for expected_hex, name, masm in rows:
            safe = re.sub(r"[^A-Za-z0-9_.-]", "_", name)
            got, err = assemble(ml64, workdir, safe, masm)
            if got is None:
                errors.append((name, err))
                continue
            got_hex = got.hex()
            if got_hex != expected_hex:
                mismatches.append((name, expected_hex, got_hex, masm))

    for name, err in errors:
        print(f"ERROR  {name}: {err}", file=sys.stderr)
    for name, want, got, masm in mismatches:
        print(f"MISMATCH  {name}", file=sys.stderr)
        print(f"    prologue  {masm}", file=sys.stderr)
        print(f"    grass     {want}", file=sys.stderr)
        print(f"    ml64      {got}", file=sys.stderr)

    checked = len(rows) - len(errors)
    if mismatches or errors:
        print(
            f"win64 unwind differential: {len(rows)} rows, {checked} assembled, "
            f"{len(mismatches)} disagree with ml64, {len(errors)} could not be "
            "assembled", file=sys.stderr)
        return 1

    print(
        f"win64 unwind differential: {len(rows)} prologues, .xdata "
        f"byte-identical to ml64 on all of them")
    return 0


if __name__ == "__main__":
    sys.exit(main())
