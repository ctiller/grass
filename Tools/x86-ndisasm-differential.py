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

import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# NDISASM prints "00000000  4C8D2D44332211    lea r13,[rel 0x11223351]".
# The target is what we check; the mnemonic text is deliberately not compared,
# because disassembler formatting (operand order, `near`, `qword`, `*1`
# elision) differs from any rendering Grass would produce and none of it is a
# fact about the encoding.
TARGET = re.compile(r"\[rel (0x[0-9a-fA-F]+)\]")

# NDISASM starts each instruction with its 8-hex-digit address in column 0, and
# wraps an instruction whose bytes do not fit onto continuation lines that are
# indented and begin with "-". Counting raw lines therefore reports a long
# instruction as several, which is how this tool first reported the two `mov`
# rows -- the only rows long enough to wrap -- as length errors when their
# targets were in fact correct.
INSTRUCTION_LINE = re.compile(r"^[0-9A-F]{8}\s")

# How many rows Tests/ISA/X86/RipCorpus.lean generates. See the check in main.
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
        parts = line.split("\t", 2)
        if len(parts) != 3:
            sys.exit(f"malformed corpus line, expected 3 fields: {line!r}")
        hexbytes, target, label = parts
        rows.append((bytes.fromhex(hexbytes), int(target), label))

    if not rows:
        sys.exit("corpus is empty; did the Lean generator run?")

    # A count the generator also knows. Without it this tool reports success on
    # a corpus that is one row, or on 1084 of 1085 with the one telling row
    # removed -- both demonstrated during review. Nothing else binds the file
    # it is handed to the repository's generator, so the count is the binding.
    if len(rows) != EXPECTED_ROWS:
        sys.exit(
            f"corpus has {len(rows)} rows, expected {EXPECTED_ROWS}. "
            "Regenerate it from the Lean corpus, or update EXPECTED_ROWS here "
            "and in the corpus module if the corpus genuinely changed."
        )

    mismatches = []
    for raw, expected, label in rows:
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
