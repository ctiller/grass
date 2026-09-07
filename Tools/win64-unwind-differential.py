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
EXPECTED_DIGEST = "01f37608b0dbdb863464569672550a06ea690ce33371e07b63db20e26a5fe82e"
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
    "distinct prologues": 107,
    "directives": 6,
    "registers pushed": 8,
    "allocation sizes": 40,
    "handler field offsets": 2,
}


def coverage_buckets(rows):
    """What the corpus exercises, from each row's name and MASM text."""
    # Keyed on the tail as well as the text, because the tail changes the
    # source ml64 is handed: the same prologue with and without a handler are
    # two inputs, and counting them as one would let a handler row be added
    # without the floor noticing.
    prologues = {(row[2], row[3]) for row in rows}
    directives, pushed, allocs = set(), set(), set()
    for masm in {row[2] for row in rows}:
        for part in (p.strip() for p in masm.split("|")):
            if part.startswith("."):
                directives.add(part.split()[0])
            if part.startswith("push "):
                pushed.add(part.split()[1])
            if part.startswith("sub rsp, "):
                allocs.add(part.split(", ")[1])
    # Counted as distinct handler-field offsets rather than as a count of
    # handler rows. Seven rows that all put the handler at byte 8 exercise one
    # placement, and the padding rule is the thing being tested: it only bites
    # when the slot count is odd. Two offsets means both parities are present.
    handler_offsets = {len(row[0]) // 2 - 8 for row in rows
                       if row[3] == "handler"}
    return {
        "distinct prologues": len(prologues),
        "directives": len(directives),
        "registers pushed": len(pushed),
        "allocation sizes": len(allocs),
        "handler field offsets": len(handler_offsets),
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


# `PROC FRAME:handler` is the only tail ml64 will emit, and it sets both handler
# bits rather than UNW_FLAG_EHANDLER alone. The handler stays EXTERN so that its
# address remains a relocation for `xdata_of` to read.
TEMPLATE_HANDLER = """\
EXTERN grasshandler:PROC
.CODE
grassprobe PROC FRAME :grasshandler
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


# IMAGE_REL_AMD64_ADDR32NB: a 32-bit RVA, which is how every address inside
# `UNWIND_INFO` and `RUNTIME_FUNCTION` is stored.
ADDR32NB = 0x0003


def section_of(obj: Path, want: str) -> tuple[bytes, list[tuple[int, int]]] | None:
    """The `.xdata` section's raw bytes and its relocations.

    The relocations are not a decoration. In an object file the handler
    address has not been resolved, so the four bytes where it will land read
    zero -- and so does the language-specific dword beside it, and so does
    the padding. Comparing those bytes against a model that predicted zero
    confirms nothing: a model that omitted the handler field entirely agrees,
    byte for byte, with one that placed it correctly, because both are
    looking at zeros.

    What separates them is the relocation, which names `grasshandler` and the
    offset the linker will write it to. That offset is a real measurement of
    where this assembler puts the handler field, and it needs no link step.
    """
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
        if name != want:
            continue
        size, ptr = struct.unpack_from("<II", data, off + 16)
        if ptr == 0 or ptr + size > len(data):
            return None
        rel_ptr, = struct.unpack_from("<I", data, off + 24)
        n_rel, = struct.unpack_from("<H", data, off + 32)
        relocs = []
        for r in range(n_rel):
            r_off = rel_ptr + r * 10
            if r_off + 10 > len(data):
                return None
            va, _sym, kind = struct.unpack_from("<IIH", data, r_off)
            relocs.append((va, kind))
        return data[ptr:ptr + size], relocs
    return None


def xdata_of(obj: Path) -> tuple[bytes, list[tuple[int, int]]] | None:
    """The `.xdata` section and its relocations."""
    return section_of(obj, ".xdata")


def check_pdata(obj: Path) -> str:
    """Complain unless `.pdata` holds one well-formed `RUNTIME_FUNCTION`.

    `RuntimeFunction.toBytes` was covered by nothing. It is checkable without a
    linker, but not from the section's bytes: every address in an object file
    is an unresolved relocation, so all twelve bytes of the entry read as the
    addend alone and a model that emitted the three fields in any order would
    produce the same zeros.

    The relocation directory is what carries the structure. One function must
    produce exactly three `ADDR32NB` relocations at offsets 0, 4 and 8 -- the
    field order and the twelve-byte stride, measured rather than assumed -- and
    the addend stored at offset 4 must be the function's length, because
    `EndAddress` is one past its last byte and `BeginAddress` is its first. The
    length is read from `.text`'s own size, which is an independent fact about
    the object rather than anything this corpus predicted.

    What this still does not reach is the table: `PdataSection.Separated` and
    the ascending order `WellFormed` requires are properties of several entries
    laid out together, and each object here holds one function. Those need a
    link step, and they remain owed.
    """
    read = section_of(obj, ".pdata")
    if read is None:
        return "no .pdata section in the object"
    data, relocs = read
    if len(data) != 12:
        return (f".pdata is {len(data)} bytes; one function should produce "
                "exactly one 12-byte RUNTIME_FUNCTION")
    offsets = sorted(off for off, _kind in relocs)
    if offsets != [0, 4, 8]:
        return (f".pdata relocations sit at {offsets}, not [0, 4, 8]; the "
                "three fields are BeginAddress, EndAddress and "
                "UnwindInfoAddress, each a 4-byte RVA")
    wrong = [f"{off:#x}" for off, kind in relocs if kind != ADDR32NB]
    if wrong:
        return f".pdata relocations at {wrong} are not ADDR32NB"
    text = section_of(obj, ".text$mn") or section_of(obj, ".text")
    if text is None:
        return "no .text section to measure the function length against"
    begin, end = struct.unpack_from("<II", data, 0)
    if begin != 0:
        return f"BeginAddress addend is {begin}, expected 0 (start of function)"
    if end != len(text[0]):
        return (f"EndAddress addend is {end} but .text is {len(text[0])} "
                "bytes; EndAddress must be one past the function's last byte")
    return ""


def check_handler_reloc(got: bytes, relocs: list[tuple[int, int]],
                        tail: str) -> str:
    """Complain unless the relocations match the tail the row declares.

    A row with no handler must carry no `.xdata` relocation at all, and a row
    with one must carry exactly one, of type ADDR32NB, at the offset just
    before the single language-specific dword. Both halves matter: the first is
    what would catch a handler leaking into a prologue that never asked for
    one, and without it this would pass just as happily on an assembler that
    emitted handlers everywhere.

    The expected offset is derived from the length ml64 produced, not from the
    model, so it stays an independent measurement. Computing it from the
    predicted bytes would let a model that mislaid the handler move the
    goalposts along with its prediction.
    """
    if tail != "handler":
        if relocs:
            return ("no handler was declared but .xdata carries "
                    f"{len(relocs)} relocation(s) at {[o for o, _ in relocs]}")
        return ""
    if len(relocs) != 1:
        kinds = sorted(k for _off, k in relocs)
        return ("expected exactly one .xdata relocation for the handler, "
                f"got {len(relocs)} (kinds {kinds})")
    off, kind = relocs[0]
    if kind != ADDR32NB:
        return f"handler relocation is type {kind:#06x}, expected ADDR32NB"
    want = len(got) - 8
    if off != want:
        return (f"handler relocation at offset {off}, but the section is "
                f"{len(got)} bytes and the handler field belongs at {want} "
                "(one language-specific dword follows it)")
    return ""


def assemble(ml64: str, workdir: Path, name: str, masm: str,
             tail: str) -> tuple[bytes | None, str]:
    """Assemble one prologue and return its `.xdata` bytes."""
    parts = [p.strip() for p in masm.split("|")]
    instructions = [p for p in parts if not p.startswith(".")]
    prologue = "\n".join("    " + p for p in parts)
    template = TEMPLATE_HANDLER if tail == "handler" else TEMPLATE
    source = template.format(
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
    read = xdata_of(obj)
    if read is None:
        return None, "no .xdata section in the object"
    got, relocs = read
    complaint = check_handler_reloc(got, relocs, tail) or check_pdata(obj)
    if complaint:
        return None, complaint
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
        if len(fields) != 4:
            print(f"malformed corpus row: {line!r}", file=sys.stderr)
            return 1
        if fields[3] not in ("none", "handler"):
            print(f"unknown tail {fields[3]!r} in row: {line!r}",
                  file=sys.stderr)
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
        for expected_hex, name, masm, tail in rows:
            safe = re.sub(r"[^A-Za-z0-9_.-]", "_", name)
            got, err = assemble(ml64, workdir, safe, masm, tail)
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
        f"byte-identical to ml64 on all of them; handler tails and .pdata "
        f"field order checked against the relocation directory")
    return 0


if __name__ == "__main__":
    sys.exit(main())
