#!/usr/bin/env python3
"""Differential check of Grass's RIP-relative encoding against NDISASM.

`docs/VALIDATION.md` section 2 layer 2 asks for comparison against independent
decoders and disassemblers. This is the disassembler half; the assembler half is
`Tools/x86-nasm-differential.py`.

It exists because the RIP-relative form is the one an assembler cannot check.
NASM computes a RIP displacement from a target address and an instruction
length, so a source line asserting a literal displacement tests NASM's
arithmetic rather than Grass's encoding. A disassembler has the opposite
property: given bytes, NDISASM prints the absolute target it computed, and that
number is exactly what the RIP contract is about.

Which matters, because `mod=00, rm=101` is the form whose meaning is unique to
64-bit mode -- in 32-bit mode the same encoding is an absolute displacement --
and it is the form behind every import call and the payload address in Spike 1.
Without this check it had no external validation at all.

## What the target number tests

The displacement is relative to the address of the *next* instruction. So
disassembled at origin 0, an instruction of length n with displacement d must
print target n + d. That single number separates three distinct mistakes:

  * resolving against the start of the instruction instead of the end;
  * resolving against the end of the displacement field rather than the end of
    the instruction -- which differ only when a trailing immediate is present,
    so the `mov` rows carrying an imm32 are the ones that tell those apart;
  * a reversed displacement byte order, which moves the target far.

NDISASM is a fallible oracle, not authority. `docs/VALIDATION.md` section 2:
"Disagreement is preserved as a finding; majority vote does not establish
truth."

Usage:
    lake env lean --run Tests/ISA/X86/RipCorpus.lean > rip.txt
    python Tools/x86-ndisasm-differential.py rip.txt

Exit status is 1 on any mismatch.
"""

import hashlib
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# NDISASM prints "00000000  4C8D2D44332211    lea r13,[rel 0x11223351]".
TARGET = re.compile(r"\[rel (0x[0-9a-fA-F]+)\]")

# Operand-size and distance keywords NDISASM prints and Grass does not model as
# text. Stripping them, along with spaces and case, leaves the part that is a
# fact about the encoding: the mnemonic, the register, and the target.
NOISE = ("qword", "dword", "word", "byte", "near", "short", "far")



def corpus_digest(text: str) -> str:
    """A digest of the corpus content, line endings normalised.

    The row count was the only binding between this tool and the Lean
    generator, and a reviewer defeated it twice: a corpus of one row reported
    success, and so did a corpus whose every row was a copy of the first, since
    the count was still right. A digest binds content, so substituting a
    same-length corpus fails.

    Changing the corpus therefore requires updating EXPECTED_DIGEST here, which
    is the reviewed edit `docs/VALIDATION.md` section 7 asks for rather than a
    silent change to what is being checked."""
    normalised = "\n".join(
        line.rstrip("\r") for line in text.splitlines() if line.strip())
    return hashlib.sha256(normalised.encode("utf-8")).hexdigest()


def normalise(text: str) -> str:
    """The comparable part of a disassembly line.

    The target alone is not enough. Both Grass's expected target and NDISASM's
    are functions of the same instruction length, so they move together: a
    reviewer stripped REX.W from all sixteen `lea` rows -- turning
    `lea rax,[rel ...]` into the different instruction `lea eax,[rel ...]` --
    and every row still agreed. Replacing all nineteen rows with identical bytes
    also passed. The register field was invisible until this compared text."""
    body = text.split(None, 2)
    body = body[2] if len(body) > 2 else ""
    lowered = body.lower()
    for word in NOISE:
        lowered = lowered.replace(word, "")
    return "".join(lowered.split())

# NDISASM starts each instruction with its 8-hex-digit address in column 0, and
# wraps an instruction whose bytes do not fit onto continuation lines that are
# indented and begin with "-". Counting raw lines therefore reports a long
# instruction as several, which is how this tool first reported the two `mov`
# rows -- the only rows long enough to wrap -- as length errors when their
# targets were in fact correct.
INSTRUCTION_LINE = re.compile(r"^[0-9A-F]{8}\s")

# The corpus this tool was last reviewed against. See corpus_digest.
EXPECTED_DIGEST = "17d42f62ab26f1f69e92aec7d13716f954827628d64faedfb08e8f0d0e1e3111"
# The coverage this tool was reviewed at. Shrinking the corpus must be a
# deliberate, reviewed edit rather than a side effect of regenerating it.
#
# The digest above detects a substituted corpus but not a smaller one: an author
# who shrinks the generator gets a digest mismatch, is told to update the
# constant, updates it, and the tool passes over the smaller corpus. A reviewer
# demonstrated it -- one `.take 1` plus a digest update turned 1085 encodings
# into 1 and still reported no disagreement. `docs/VALIDATION.md` section 7's
# ratchet is meant to prevent exactly that, and this is it applied to corpora.
EXPECTED_ROWS = 19



def find_tool(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    for candidate in (
        Path.home() / f"AppData/Local/bin/NASM/{name}.exe",
        Path(f"C:/Program Files/NASM/{name}.exe"),
    ):
        if candidate.exists():
            return str(candidate)
    sys.exit(f"{name} not found on PATH or in the usual install locations")


def disassemble(ndisasm: str, raw: bytes) -> tuple[str, int] | None:
    """Disassemble one instruction at origin 0; return its text and the count
    of instructions NDISASM found.

    The count matters: if Grass's bytes decode as more than one instruction,
    the length is wrong even when the first line looks right."""
    with tempfile.TemporaryDirectory() as tmp:
        binary = Path(tmp) / "insn.bin"
        binary.write_bytes(raw)
        result = subprocess.run(
            [ndisasm, "-b", "64", str(binary)], capture_output=True, text=True
        )
        if result.returncode != 0:
            return None
        lines = [ln for ln in result.stdout.splitlines() if ln.strip()]
        starts = [ln for ln in lines if INSTRUCTION_LINE.match(ln)]
        return ("\n".join(lines), len(starts))


def main() -> int:
    if len(sys.argv) != 2:
        sys.exit("usage: x86-ndisasm-differential.py <rip.txt>")
    ndisasm = find_tool("ndisasm")

    rows = []
    for line in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        parts = line.split("\t", 3)
        if len(parts) != 4:
            sys.exit(f"malformed corpus line, expected 4 fields: {line!r}")
        hexbytes, target, expected_text, label = parts
        rows.append((bytes.fromhex(hexbytes), int(target, 16), expected_text, label))

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

    mismatches = []
    for raw, expected, expected_text, label in rows:
        got = disassemble(ndisasm, raw)
        if got is None:
            mismatches.append((label, raw.hex(), "ndisasm refused the bytes"))
            continue
        text, count = got
        if count != 1:
            mismatches.append((
                label, raw.hex(),
                f"decoded as {count} instructions, so the length is wrong:\n{text}",
            ))
            continue
        found = TARGET.search(text)
        if not found:
            mismatches.append((
                label, raw.hex(),
                f"no RIP-relative target in the disassembly: {text.strip()}",
            ))
            continue
        actual = int(found.group(1), 16)
        if actual != expected:
            mismatches.append((
                label, raw.hex(),
                f"target {actual:#x}, expected {expected:#x} "
                f"(instruction length {len(raw)}); {text.strip()}",
            ))
            continue
        got = normalise(text)
        if not got.startswith(expected_text):
            mismatches.append((
                label, raw.hex(),
                f"operands {got!r} do not start with the predicted "
                f"{expected_text!r}",
            ))

    print(f"x86 NDISASM differential: {len(rows)} RIP-relative encodings, "
          f"{len(rows) - len(mismatches)} agree")

    if mismatches:
        print(f"\n{len(mismatches)} mismatch(es):\n")
        for label, hexed, detail in mismatches[:40]:
            print(f"  {label}")
            print(f"    grass: {hexed}")
            print(f"    {detail}")
        return 1

    print("no disagreement")
    return 0


if __name__ == "__main__":
    sys.exit(main())
