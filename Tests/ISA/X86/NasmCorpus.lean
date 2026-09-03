import Tests.ISA.X86.CorpusCommon

/-!
# NASM differential corpus

Emits, for every addressing form this profile can encode, the bytes Grass
produces and the NASM source line that should assemble to them.
`Tools/x86-nasm-differential.py` feeds the source to NASM and compares.

This is `docs/VALIDATION.md` §2 layer 2 — "compare encoders, decoders,
assemblers, disassemblers, loaders, emulators, and API observations where
independent tools exist". It is the only check in the tree that can tell whether
the model is about x86-64 at all: every theorem in `Grass/ISA/X86/**` relates
Grass's own definitions to each other, and a model with two ModR/M fields
transposed satisfies all of them.

NASM is a fallible oracle, not authority. `docs/VALIDATION.md` §2: "Tools and
hardware are fallible oracles. Disagreement is preserved as a finding; majority
vote does not establish truth." A mismatch is a finding against Grass *or*
against NASM, resolved by reading the manual, not by changing Grass to match.

## Why the displacement is `0x11223344`

Four distinct non-zero bytes, so a byte-order error is visible rather than
palindromic, and too large for a signed 8-bit displacement — which matters
because Grass's encoder always emits `disp32` and NASM emits the shortest form.
With a displacement NASM cannot shorten, the two agree exactly and a byte
comparison is meaningful. A displacement of `8` would make NASM choose `disp8`
and produce a legitimately different, shorter encoding; that is a real
difference in policy, not a defect, and it is excluded here rather than papered
over. `Tools/x86-nasm-differential.py` documents the same choice.

## Coverage

- `lea` over every base register (16), and over every base × index × scale
  combination that is encodable (16 × 15 × 4 — `rsp` is excluded as an index
  because no encoding of it exists);
- index-only and absolute forms, which are the SIB no-base cases;
- `call qword ptr` and `mov dword ptr` to exercise a `/digit` opcode extension
  and an instruction carrying an immediate after the displacement.

RIP-relative forms are absent here, and are checked instead by
`Tests/ISA/X86/RipCorpus.lean` against NDISASM. NASM computes a RIP
displacement from a target address and an instruction length, so a source line
asserting a literal displacement would test NASM's arithmetic rather than
Grass's encoding; a disassembler prints the target it computed, which is the
number the RIP contract is actually about.
-/

namespace Grass.Tests.ISA.X86.Nasm

open Grass.Std.Logical Grass.ISA.X86 Grass.Tests.ISA.X86.Corpus

/-- The NASM address expression for a memory operand.

`ripRelative` has no faithful literal spelling in NASM source. No corpus row
below builds one, so this case is unreachable; it renders as a marker that would
fail loudly at NASM rather than silently assembling to something else. The
RIP-relative forms are covered by `Tests/ISA/X86/RipCorpus.lean`. -/
def nasmAddr : MemOperand → String
  | .base b d => "[" ++ nasmName b ++ "+" ++ hex32 d ++ "]"
  | .baseIndex b i s d =>
      "[" ++ nasmName b ++ "+" ++ nasmName i ++ "*" ++ scaleText s ++ "+" ++ hex32 d ++ "]"
  | .indexOnly i s d =>
      -- `nosplit` suppresses NASM's rewriting of a no-base scaled index into a
      -- base form: it emits `[rax+d]` for `[rax*1+d]` and `[rax+rax*1+d]` for
      -- `[rax*2+d]`. Those are correct encodings of the same address and a
      -- legitimate assembler policy, but they are not the encoding under test,
      -- and comparing against them would report NASM's optimizer rather than
      -- Grass's encoder. With `nosplit` the two agree byte for byte.
      "[nosplit " ++ nasmName i ++ "*" ++ scaleText s ++ "+" ++ hex32 d ++ "]"
  | .absolute d => "[" ++ hex32 d ++ "]"
  | .ripRelative _ => "<rip-relative: not expressible as a NASM literal>"

/-- One corpus row: the NASM source line and the bytes Grass emits for it. -/
structure Row where
  /-- The NASM source line. -/
  source : String
  /-- Grass's encoding, as lowercase hex. -/
  bytes : String

/-- Every base register, with a 32-bit displacement. -/
def baseRows : List Row :=
  Gpr.all.filterMap fun b =>
    let m := MemOperand.base b disp
    (leaR64 .rax m).map fun i =>
      { source := "lea rax, " ++ nasmAddr m, bytes := hexBytes i.toBytes }

/-- Every destination register over one base, to exercise `REX.R` and the
`reg` field independently of the address. -/
def destRows : List Row :=
  Gpr.all.filterMap fun d =>
    let m := MemOperand.base .rbx disp
    (leaR64 d m).map fun i =>
      { source := "lea " ++ nasmName d ++ ", " ++ nasmAddr m, bytes := hexBytes i.toBytes }

/-- Every encodable base × index × scale. -/
def baseIndexRows : List Row :=
  Gpr.all.flatMap fun b =>
    Gpr.all.flatMap fun idx =>
      [Scale.s1, Scale.s2, Scale.s4, Scale.s8].filterMap fun s =>
        let m := MemOperand.baseIndex b idx s disp
        (leaR64 .rax m).map fun i =>
          { source := "lea rax, " ++ nasmAddr m, bytes := hexBytes i.toBytes }

/-- Index-only forms: the SIB no-base case with an index. -/
def indexOnlyRows : List Row :=
  Gpr.all.flatMap fun idx =>
    [Scale.s1, Scale.s2, Scale.s4, Scale.s8].filterMap fun s =>
      let m := MemOperand.indexOnly idx s disp
      (leaR64 .rax m).map fun i =>
        { source := "lea rax, " ++ nasmAddr m, bytes := hexBytes i.toBytes }

/-- The absolute form: SIB with neither base nor index. -/
def absoluteRows : List Row :=
  let m := MemOperand.absolute disp
  (leaR64 .rax m).toList.map fun i =>
    { source := "lea rax, " ++ nasmAddr m, bytes := hexBytes i.toBytes }

/-- `call qword ptr m` over every base: a `/digit` opcode extension, and a
64-bit-default operand size that must not acquire a `REX.W`. -/
def callRows : List Row :=
  Gpr.all.filterMap fun b =>
    let m := MemOperand.base b disp
    (callMem64 m).map fun i =>
      { source := "call qword " ++ nasmAddr m, bytes := hexBytes i.toBytes }

/-- `mov dword ptr m, imm32` over every base: an immediate following the
displacement, which is where a length or order error shows up. -/
def movRows : List Row :=
  Gpr.all.filterMap fun b =>
    let m := MemOperand.base b disp
    (movMem32Imm32 m immValue).map fun i =>
      { source := "mov dword " ++ nasmAddr m ++ ", " ++ hex32 immValue,
        bytes := hexBytes i.toBytes }

/-- The whole corpus. -/
def corpus : List Row :=
  baseRows ++ destRows ++ baseIndexRows ++ indexOnlyRows ++ absoluteRows ++
    callRows ++ movRows

end Grass.Tests.ISA.X86.Nasm

/-- Print the corpus as tab-separated `bytes<TAB>source` lines.

Top level rather than in the namespace because `lake env lean --run` looks for
`main` there. -/
def main : IO Unit := do
  for r in Grass.Tests.ISA.X86.Nasm.corpus do
    IO.println (r.bytes ++ "\t" ++ r.source)
