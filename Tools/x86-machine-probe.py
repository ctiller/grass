#!/usr/bin/env python3
"""Execute Grass's encoded instructions on the real processor and compare.

`docs/VALIDATION.md` section 2 layer 3: "Physical probes: execute generated
instruction/API cases on named CPU/OS/GPU profiles and compare complete declared
effects."

Every other check in this repository compares Grass against a document or
against another tool. This one compares it against silicon, and it is the only
layer that can settle a question the manuals leave ambiguous -- which matters
right now, because `Grass/ISA/X86/Sources.lean` records the AMD manual as
unretrievable and no citation anchor is confirmed.

Hardware is a fallible oracle, not authority. `docs/VALIDATION.md` section 2:
"Tools and hardware are fallible oracles. Disagreement is preserved as a
finding; majority vote does not establish truth." A failing probe is a finding
against Grass, against this harness, or a genuine erratum, and is resolved by
reading the manual -- not by editing the model until it matches.

## How a probe runs

NASM assembles a wrapper that loads a register file from a buffer, executes the
bytes under test, and stores the register file and RFLAGS back. Only the bytes
under test come from Grass; everything around them comes from NASM, so a bug in
Grass's encoder cannot also write its own scaffolding.

RSP is never loaded from the buffer. It is the harness's own stack, and a probe
that redirected it would take the process with it.

## Isolation

An instruction under test can fault, and `docs/VALIDATION.md` section 4 requires
probe processes to be isolated when faults or hangs are possible. Each probe
therefore runs in a child process. Windows sets a crashed child's exit code to
the NTSTATUS, so a fault is *reported with its class* rather than lost: an
illegal instruction comes back as 0xC000001D, an access violation as
0xC0000005. That makes a faulting probe data rather than a crash, which is what
the fault-declaration facet of `docs/INSTRUCTIONS.md` section 3 will need.

A timeout guards against a probe that does not return at all.

## Scope

User mode only. Ring 0 instructions cannot be reached from a process and are not
attempted here; they need a bare-metal or hypervisor harness.

Usage:
    lake env lean --run Tests/ISA/X86/MachineProbes.lean > probes.txt
    python Tools/x86-machine-probe.py probes.txt

Exit status is 1 if any probe disagrees with the model.
"""

import platform
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REGS = ("rax rcx rdx rbx rsp rbp rsi rdi "
        "r8 r9 r10 r11 r12 r13 r14 r15").split()
RSP = 4  # never loaded or compared: it is the harness's own stack

# How many probes Tests/ISA/X86/MachineProbes.lean generates. Without this the
# runner reports success on a truncated corpus.
EXPECTED_ROWS = 21

PROBE_TIMEOUT_SECONDS = 30


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


def wrapper_source(insn_hex: str) -> str:
    """NASM source for the probe wrapper around one instruction.

    The buffer is 17 qwords: sixteen GPRs in encoding order, then RFLAGS.
    RFLAGS is captured first, before any instruction that could disturb it."""
    body = ", ".join("0x" + insn_hex[i:i + 2] for i in range(0, len(insn_hex), 2))
    loads = "\n".join(
        f"  mov {REGS[i]}, [rax+8*{i}]" for i in range(16) if i not in (0, RSP))
    stores = "\n".join(
        f"  mov [rax+8*{i}], {REGS[i]}" for i in range(1, 16) if i != RSP)
    return f"""BITS 64
  push rbx
  push rbp
  push rsi
  push rdi
  push r12
  push r13
  push r14
  push r15
  push rcx
  mov rax, rcx
{loads}
  mov rax, [rax+8*0]
  db {body}
  pushfq
  push rax
  mov rax, [rsp+16]
{stores}
  mov rcx, [rsp]
  mov [rax+8*0], rcx
  mov rcx, [rsp+8]
  mov [rax+8*16], rcx
  add rsp, 24
  pop r15
  pop r14
  pop r13
  pop r12
  pop rdi
  pop rsi
  pop rbp
  pop rbx
  ret
"""


WORKER = r'''
import ctypes, ctypes.wintypes as wt, sys
k32 = ctypes.WinDLL('kernel32', use_last_error=True)
k32.VirtualAlloc.restype = ctypes.c_void_p
k32.VirtualAlloc.argtypes = [ctypes.c_void_p, ctypes.c_size_t, wt.DWORD, wt.DWORD]
code = open(sys.argv[1], 'rb').read()
addr = k32.VirtualAlloc(None, len(code), 0x3000, 0x40)
if not addr:
    sys.exit("VirtualAlloc failed")
ctypes.memmove(addr, code, len(code))
fn = ctypes.CFUNCTYPE(None, ctypes.POINTER(ctypes.c_uint64))(addr)
buf = (ctypes.c_uint64 * 17)()
for i, v in enumerate(sys.argv[2].split(',')):
    buf[i] = int(v, 16)
fn(buf)
print(','.join(f'{buf[i]:016x}' for i in range(17)))
'''


def run_probe(worker: Path, binary: Path, before: list[int]) -> tuple[str, list[int] | None]:
    """Run one probe in a child process. Returns (status, register file)."""
    argv = [sys.executable, str(worker), str(binary),
            ",".join(f"{v:016x}" for v in before)]
    try:
        result = subprocess.run(argv, capture_output=True, text=True,
                                timeout=PROBE_TIMEOUT_SECONDS)
    except subprocess.TimeoutExpired:
        return ("timeout", None)
    if result.returncode != 0:
        # Windows reports a crashed child's NTSTATUS as its exit code, so the
        # fault class survives. Negative values are the same code sign-extended.
        code = result.returncode & 0xFFFFFFFF
        known = {
            0xC000001D: "STATUS_ILLEGAL_INSTRUCTION",
            0xC0000005: "STATUS_ACCESS_VIOLATION",
            0xC0000094: "STATUS_INTEGER_DIVIDE_BY_ZERO",
            0xC000008C: "STATUS_ARRAY_BOUNDS_EXCEEDED",
            0xC0000096: "STATUS_PRIVILEGED_INSTRUCTION",
        }
        name = known.get(code, "")
        detail = f"{code:#010x}" + (f" ({name})" if name else "")
        return (f"faulted {detail}", None)
    line = result.stdout.strip().splitlines()[-1]
    return ("ok", [int(v, 16) for v in line.split(",")])


def describe_host() -> list[str]:
    """Identification `docs/VALIDATION.md` section 3 requires a campaign to
    record. Microcode revision is not exposed to a user-mode process on Windows
    and is reported as unknown rather than guessed."""
    lines = [
        f"machine:   {platform.machine()}",
        f"os:        {platform.system()} {platform.release()} ({platform.version()})",
        f"python:    {platform.python_version()}",
        "microcode: unknown (not readable from user mode)",
    ]
    try:
        out = subprocess.run(
            ["reg", "query",
             r"HKLM\HARDWARE\DESCRIPTION\System\CentralProcessor\0"],
            capture_output=True, text=True, timeout=15).stdout
        for key in ("ProcessorNameString", "Identifier", "VendorIdentifier"):
            for raw in out.splitlines():
                if key in raw:
                    lines.append(f"{key.lower():10} {raw.split('    ')[-1].strip()}")
                    break
    except Exception:
        lines.append("cpu:       unavailable")
    return lines


def main() -> int:
    if len(sys.argv) != 2:
        sys.exit("usage: x86-machine-probe.py <probes.txt>")
    nasm = find_tool("nasm")

    rows = []
    for line in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) != 6:
            sys.exit(f"malformed probe line, expected 6 fields: {line!r}")
        label, insn, before, after, kind, note = parts
        rows.append((label, insn,
                     [int(v, 16) for v in before.split(",")],
                     [int(v, 16) for v in after.split(",")],
                     kind, note))

    if len(rows) != EXPECTED_ROWS:
        sys.exit(f"corpus has {len(rows)} probes, expected {EXPECTED_ROWS}")

    print("x86 physical probe campaign")
    for line in describe_host():
        print(f"  {line}")
    print()

    agree, disagree, exceptions = [], [], []
    with tempfile.TemporaryDirectory() as tmp:
        worker = Path(tmp) / "worker.py"
        worker.write_text(WORKER, encoding="ascii")
        for label, insn, before, expected, kind, note in rows:
            asm = Path(tmp) / "probe.asm"
            binary = Path(tmp) / "probe.bin"
            asm.write_text(wrapper_source(insn), encoding="ascii")
            built = subprocess.run(
                [nasm, "-f", "bin", "-o", str(binary), str(asm)],
                capture_output=True, text=True)
            if built.returncode != 0:
                disagree.append((label, insn, note,
                                 "wrapper failed to assemble: "
                                 + built.stderr.strip()))
                continue
            status, actual = run_probe(worker, binary, before)
            if actual is None:
                disagree.append((label, insn, note, status))
                continue
            differing = [
                (REGS[i], expected[i], actual[i])
                for i in range(16)
                if i != RSP and expected[i] != actual[i]
            ]
            if differing:
                detail = "; ".join(
                    f"{name}: model {e:#018x}, cpu {a:#018x}"
                    for name, e, a in differing)
                disagree.append((label, insn, note, detail))
            elif kind == "exception":
                exceptions.append((label, insn, note))
            else:
                agree.append(label)

    print(f"{len(rows)} probes: {len(agree)} agree with the model, "
          f"{len(exceptions)} confirm a documented exception, "
          f"{len(disagree)} disagree")

    for label, insn, note in exceptions:
        print(f"\n  exception confirmed on this processor: {label}")
        print(f"    bytes: {insn}")
        print(f"    {note}")

    if disagree:
        print(f"\n{len(disagree)} disagreement(s):\n")
        for label, insn, note, detail in disagree:
            print(f"  {label}")
            print(f"    bytes: {insn}")
            print(f"    {detail}")
            print(f"    note:  {note}")
        return 1

    print("\nno disagreement between the model and this processor")
    return 0


if __name__ == "__main__":
    sys.exit(main())
