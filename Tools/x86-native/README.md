# x86 native differential validation

The bounded [scratch-stack campaign](STACK.md) extends this register campaign
with successful PUSH/allocation effects and complete declared scratch snapshots.

This is the verification side lane following `spikes`, initially against main
`28e5767b`. It exercises public encoders and register write-back on the host CPU.
It does not certify instruction semantics or close citation/proof obligations.

## Implementation direction and bootstrap

The intended implementation is a Grass program. The C worker and Python drivers
are temporary bootstrap infrastructure and an independent comparison oracle,
not the permanent verification architecture. The existing Lean corpus generators
do not make the runner Grass-hosted: the target state setup, capture, comparison
and reporting still execute outside Grass today.

Move the protected execution/capture program onto the same authored-source,
lowering and artifact path that `spikes` develops. Its specification should
describe the capture boundary and permitted harness writes separately from the
instruction being tested. No complete emitted PE/loaded-code certificate is
available yet. The first native artifact should be a minimal Grass-generated PE
using the same production entry/import/emission path as Hello World, with a
bounded exit/status/output observation driven by the bootstrap process. Compare
its exact emitted bytes, entry, imports and prologue against the current oracle.
Move capture, process isolation, OS exception adapters, corpus driving and
reporting into Grass as the required verified platform capabilities become
available; do not expand every VEH/allocation provider ahead of that path.
A hand-written
PE writer or a second long-lived compiler path is not a substitute for those
shared facilities. Linux and bare-metal adapters follow their platform owners.

Bootstrap acceptance requires the old and new implementations to run the same
cases and compare complete declared observations, including deliberately wrong
expectations and harness-failure controls. Retain a small independently produced
capture path and independent encoding/known-answer checks: producing the harness
and test body with the same encoder can hide a shared defect. Running a
Grass-generated harness validates an artifact; it does not prove the ISA model
itself. Any initially unchecked Grass construction must retain its explicit
missing-check status rather than acquire a `VerifiedProgram` certificate from
successful tests. Retire bootstrap responsibilities only when the replacement
has demonstrated the corresponding observation and failure behavior.

While the shared artifact path is incomplete, prioritize its concrete missing
capabilities with `spikes` and keep C/Python changes limited to fixes or the
minimum oracle support needed to validate that transition. The current working
campaign remains available throughout the bootstrap loop.

From Git Bash at the repository root, with the pinned Lean toolchain, Python 3
and MSVC x64 (Visual Studio Installer must provide `vswhere.exe`):

```bash
lake build Tests.ISA.X86.NativeCorpus
bash Tools/x86-native/build.sh
python Tools/x86-native/run.py --worker target/x86-native/windows.exe --output target/x86-native/campaign-1
```

`build.sh [output-directory]` supports paths containing spaces. Set `VSWHERE`
to an alternate installer-discovery executable if necessary. The script invokes
the vendor's `vcvars64.bat` through `cmd.exe` to obtain the compiler environment;
it does not require PowerShell. This builds the Windows adapter, not a Linux
adapter; unsupported hosts fail explicitly.

Use a new output directory for every run. Outputs contain the generated TSV,
CPU/OS and revision metadata, worker/source/corpus hashes, all native observations
including mismatches, and a summary. Build products and local evidence live under
ignored `target/`. Preserve the whole directory when reporting a finding.
Any mismatch, unexpected fault, hang, malformed result, missing tool, failed
control, or changed population returns nonzero. Each case runs in a separate
process with a five-second deadline. This isolates crashes and hangs; it is not
a security sandbox for adversarial code. Run only the repository-generated cases.
The coverage fingerprint binds labels, incoming state/flags and prediction basis;
it excludes emitted bytes and expected outputs so model changes reach comparison.

## What is compared

The population is generated once in
[`NativeCorpus.lean`](../../Tests/ISA/X86/NativeCorpus.lean):

* 450 register MOV cases: every pair among 15 non-RSP GPRs, 32 and 64 bits,
  including aliasing and both REX register fields. Distinct initial register
  values expose wrong operand selection; nonzero high halves expose missed
  zero-extension. Predictions call Grass's `writeBack`.
* 420 SUB/CMP immediate cases: those 15 destinations, both widths, signed imm8
  endpoints (0, 127, -128, -1) and imm32 endpoints (maximum, minimum, -1).
  Emission calls `ImmediateArithmetic.encode`; interpretation calls its `toInt`.
  The 210 SUB predictions use **test-local reference arithmetic**, not an
  existing whole-instruction state transition. The 210 CMP cases check only
  completion and GPR nonmutation; without flag predictions they cannot detect a
  wrong immediate value or validate compare semantics. Reports separate them.

All 15 initialized GPRs are compared, including unchanged registers. RSP is
captured at entry and exit and checked unchanged. It is not a corpus input.
MOV cases compare CF/PF/AF/ZF/SF/OF preservation from a deliberately set initial
pattern. Arithmetic flag results are recorded but unchecked: no arithmetic flag
semantics is claimed. Other RFLAGS bits, SIMD/x87 state and memory are outside
this campaign's declared observation surface. The single initial value pattern
does not cover arithmetic zero/carry/overflow partitions exhaustively.

The legacy [`MachineProbes.lean`](../../Tests/ISA/X86/MachineProbes.lean) is a
useful spare part, but is not imported: its BSF-zero expectation assigns a
specific undefined destination, and some hand-authored exceptions are not model
predictions. An undefined result must use an explicit comparison mask/admissible
set in a future protocol, never silently become a required hardware value.

## Windows capture and controls

The worker allocates a page RW, installs bytes bracketed by INT3, changes it to
RX and flushes the instruction cache. A vectored exception handler recognizes
the entry marker by exact address, initializes GPRs and arithmetic flags in the
Windows CONTEXT, and resumes directly at the bytes under test. The handler
recognizes completion only at the exact trailing marker. Faults inside the body
retain their exception code, exception address, RIP, GPRs and flags before any
unwinding. Exceptions outside the body are not mislabelled as instruction faults.
The child exits after capture; it never restores arbitrary callee-saved values
through an unwinder. No assembler-generated instruction wrapper is required.

Every campaign first runs independent harness controls: NOP state preservation,
deliberately wrong register, flag, completion exception and RIP expectations,
UD2, user-mode HLT, an INT3
inside the body, and an infinite loop timeout. These are reported separately
from Grass comparisons. Capture uses an exception boundary, not instruction
single-stepping; control flow that escapes the body is outside this version.

Microsoft documents that VEH runs before stack unwinding in
[Vectored Exception Handling](https://learn.microsoft.com/en-us/windows/win32/debug/vectored-exception-handling).
The ISA reference is Intel's [SDM collection](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html),
Volume 1 section 3.4.1.1 (general-purpose registers), Volume 2 MOV/SUB/CMP/INT/UD
entries. These links explain this harness; they do not change Grass's pinned
citation ledger or repair the existing AMD retrieval debt.

## Adapter boundary and next work

TSV v1 columns are label, instruction hex, 16 comma-separated input GPR values,
16 expected GPR values, incoming flags, expected flags (`-` means unchecked),
and prediction basis. GPR order is RAX RCX RDX RBX RSP RBP RSI RDI R8..R15.
Values are unsigned hex except RSP, which must be `-` in both state columns
(serialized as JSON null in retained cases). It means host-controlled input and
an unchanged-from-entry output constraint, not an ignored arbitrary value.
Native JSON has status (`completed` or `fault`), raw
platform exception, exception-address offset, raw RIP offset, entry RSP, flags
and all 16 registers. Parent-generated statuses distinguish timeout and harness
or protocol failure from an observed instruction fault. Windows breakpoint RIP
conventions remain raw and are not normalized into an architectural fault PC.
Successful completion requires the Windows breakpoint code and both raw offsets
equal to the body length.

`spikes-linux` and `spikes-bare-metal` have no released spike handoff or execution
adapter yet. Their bring-up remains theirs. Reuse the generated cases and
comparison layer when they supply a Linux signal/ucontext adapter or bare-metal
exception/serial transport; do not count QEMU TCG as physical CPU evidence.
Windows NTSTATUS must remain alongside any future normalized x86 fault class;
Linux signal numbers alone are not a portable vector mapping.

The next bounded additions follow `spikes`: a mapped scratch stack for RSP
allocation and PUSH effects, mapped memory and access-fault snapshots for
`movReg32Mem`/Store32, then flags compared against published instruction
semantics. Such additions need entry/exit memory captures, permission maps,
address relocation and explicit undefined-bit masks. They cannot be obtained by
simply allowing arbitrary RSP or memory operands in this version. Repeat on
identified Intel and AMD hosts; microcode currently remains explicitly unknown,
and the CPUID hypervisor bit alone cannot establish physical execution.
