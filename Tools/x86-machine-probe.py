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
runs in a child process, and the child installs a vectored exception handler
that terminates with the fault's own NTSTATUS the moment a hardware fault
arrives.

That handler is not decoration. Without it every fault reported 0xC0000005:
ctypes wraps the foreign call in SEH, and the wrapper faults with nine unpopped
pushes and callee-saved registers full of test values, so unwinding dies on the
corrupted stack with a *second*, genuine access violation -- and that is the
code the parent saw. A reviewer measured UD2, HLT and INT3 all reporting
0xC0000005, which made three entries of the table below unreachable. A vectored
handler runs before any unwinding, so the original code survives: UD2 reports
0xC000001D, HLT 0xC0000096, INT3 0x80000003. The handler passes anything outside
the hardware-fault set through, so it cannot swallow the interpreter's own
exception handling.

That makes a faulting probe data rather than a crash, which is what the
fault-declaration facet of `docs/INSTRUCTIONS.md` section 3 will need.

A timeout guards against a probe that does not return at all.

## Scope

User mode only. Ring 0 instructions cannot be reached from a process and are not
attempted here; they need a bare-metal or hypervisor harness.

Usage:
    lake env lean --run Tests/ISA/X86/MachineProbes.lean > probes.txt
    python Tools/x86-machine-probe.py probes.txt

Exit status is 1 if any probe disagrees with the model.
"""

import hashlib
import platform
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REGS = ("rax rcx rdx rbx rsp rbp rsi rdi "
        "r8 r9 r10 r11 r12 r13 r14 r15").split()
RSP = 4  # never loaded or compared: it is the harness's own stack

# The corpus this tool was last reviewed against. See corpus_digest.
EXPECTED_DIGEST = "985e0209048fd6c3ca5670c0f12ec27a1dd18c71c2ccb53aaaf1c8bc3f125105"

PROBE_TIMEOUT_SECONDS = 30



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


TEMPLATE = r"""; probe(buf in rcx). buf is 17 qwords: 16 GPRs in encoding order, then RFLAGS.
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
  ; Report the stack pointer the probe left behind, so a probe that moved it is
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
"""


def wrapper_source(insn_hex: str) -> str:
    """NASM source for the probe wrapper around one instruction.

    The buffer is 17 qwords: sixteen GPRs in encoding order, then RFLAGS. Slot 4
    is RSP: it is not loaded from the buffer, and on the way out it reports the
    stack pointer the probe left behind.

    Callee-saved state, the buffer pointer and the return address live in a save
    area inside this allocation, addressed RIP-relatively. None of it is on the
    stack, because the stack is exactly what a probe may move: parking the
    harness's own state there is why an ordinary `push rax` used to be reported
    as a processor fault, and why a `mov [rsp], rax` overwrote the return
    address and crashed the child.

    Incoming flags come from slot 16, so the state before the instruction is
    controlled rather than whatever the interpreter happened to leave. Outgoing
    flags survive the stack restore because `mov` does not modify flags.
    """
    body = ", ".join("0x" + insn_hex[i:i + 2] for i in range(0, len(insn_hex), 2))
    loads = "\n".join(
        f"  mov {REGS[i]}, [rax+8*{i}]" for i in range(16) if i not in (0, RSP))
    stores = "\n".join(
        f"  mov [rax+8*{i}], {REGS[i]}" for i in range(1, 16) if i != RSP)
    return "BITS 64\n" + TEMPLATE.format(body=body, loads=loads, stores=stores)


WORKER = r'''
import ctypes, ctypes.wintypes as wt, sys
k32 = ctypes.WinDLL('kernel32', use_last_error=True)
k32.VirtualAlloc.restype = ctypes.c_void_p
k32.VirtualAlloc.argtypes = [ctypes.c_void_p, ctypes.c_size_t, wt.DWORD, wt.DWORD]


class EXCEPTION_RECORD(ctypes.Structure):
    pass


EXCEPTION_RECORD._fields_ = [
    ("ExceptionCode", wt.DWORD), ("ExceptionFlags", wt.DWORD),
    ("ExceptionRecord", ctypes.POINTER(EXCEPTION_RECORD)),
    ("ExceptionAddress", ctypes.c_void_p), ("NumberParameters", wt.DWORD),
    ("ExceptionInformation", ctypes.c_ulonglong * 15)]


class EXCEPTION_POINTERS(ctypes.Structure):
    _fields_ = [("ExceptionRecord", ctypes.POINTER(EXCEPTION_RECORD)),
                ("ContextRecord", ctypes.c_void_p)]


HANDLER = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.POINTER(EXCEPTION_POINTERS))

# Hardware faults a probe can raise. Anything else -- a Python-level exception,
# a C++ throw inside the interpreter -- is passed through, so this handler
# cannot swallow the interpreter's own exception handling.
PROBE_FAULTS = {0xC0000005, 0xC000001D, 0xC0000094, 0xC0000096, 0xC000008C,
                0xC0000090, 0xC0000091, 0xC0000093, 0xC00000FD, 0x80000003}


@HANDLER
def veh(info):
    code = info.contents.ExceptionRecord.contents.ExceptionCode
    if code in PROBE_FAULTS:
        # Terminate now, before any unwinding. The wrapper faulted with unpopped
        # pushes, so letting SEH unwind produces a second access violation that
        # would be reported instead of this one.
        k32.TerminateProcess(k32.GetCurrentProcess(), code)
    return 0  # EXCEPTION_CONTINUE_SEARCH


# argtypes matter: without them the 64-bit callback pointer is truncated and the
# handler is never installed, which is how this looked like it did not work.
k32.AddVectoredExceptionHandler.restype = ctypes.c_void_p
k32.AddVectoredExceptionHandler.argtypes = [ctypes.c_ulong, HANDLER]
k32.GetCurrentProcess.restype = ctypes.c_void_p
k32.TerminateProcess.argtypes = [ctypes.c_void_p, wt.UINT]
if not k32.AddVectoredExceptionHandler(1, veh):
    sys.exit("AddVectoredExceptionHandler failed")

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
            0x80000003: "STATUS_BREAKPOINT",
            0xC00000FD: "STATUS_STACK_OVERFLOW",
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
        if len(parts) != 8:
            sys.exit(f"malformed probe line, expected 8 fields: {line!r}")
        label, insn, before, after, kind, note, flags_in, flags_out = parts
        rows.append((label, insn,
                     [int(v, 16) for v in before.split(",")] + [int(flags_in, 16)],
                     [int(v, 16) for v in after.split(",")],
                     kind, note,
                     None if flags_out == "-" else int(flags_out, 16)))

    actual_digest = corpus_digest(
        Path(sys.argv[1]).read_text(encoding="utf-8"))
    if actual_digest != EXPECTED_DIGEST:
        sys.exit(
            f"corpus digest {actual_digest} does not match the reviewed "
            f"{EXPECTED_DIGEST}. Regenerate it from the Lean corpus, or update "
            "EXPECTED_DIGEST here if the corpus genuinely changed."
        )

    print("x86 physical probe campaign")
    for line in describe_host():
        print(f"  {line}")
    print()

    agree, disagree, exceptions = [], [], []
    with tempfile.TemporaryDirectory() as tmp:
        worker = Path(tmp) / "worker.py"
        worker.write_text(WORKER, encoding="ascii")
        for label, insn, before, expected, kind, note, flags_out in rows:
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
            if flags_out is not None and actual[16] != flags_out:
                differing.append(("rflags", flags_out, actual[16]))
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
