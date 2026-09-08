import Tests.ISA.X86.CorpusCommon

/-!
# RIP-relative disassembly corpus

The RIP-relative form is the one this profile cannot check against an
assembler, and it is the form Spike 1 depends on most: every import call and the
payload address go through `mod=00, rm=101`. The NASM differential skipped it
because NASM computes a RIP displacement from a target address and an
instruction length, so a source line asserting a literal displacement would test
NASM's arithmetic rather than Grass's encoding.

A disassembler does not have that problem, and it checks something an assembler
could not: **NDISASM prints the absolute target it computed**, so comparing
against it tests the part of the RIP contract that is easy to get wrong.

## What the expected target actually tests

The displacement is relative to the address of the *next* instruction, not to
the displacement field and not to the start of the instruction. So disassembled
at origin 0, an instruction of length `n` with displacement `d` must print
target `n + d`.

That single number is sensitive to three separate mistakes, which is why it is
worth more than a byte comparison here:

- resolving against the start of the instruction instead of the end (off by
  `n`);
- resolving against the end of the *displacement field* rather than the end of
  the instruction, which differs exactly when a trailing immediate is present —
  so the `mov` rows below, which carry an `imm32` after the displacement, are
  the ones that separate those two readings;
- getting the displacement's byte order backwards, which moves the target by a
  large and obvious amount.

An NDISASM differential consumed this and checked each row. It was removed on
2026-09-08, so this corpus currently has no consumer; its replacement as a Lean
test under `Tests/ISA/X86/**` is tracked against c-x86 (c-agent:78).
-/

namespace Grass.Tests.ISA.X86.Rip

open Grass.Std.Logical Grass.ISA.X86 Grass.Tests.ISA.X86.Corpus

/-- One RIP-relative row: Grass's bytes, the target it predicts, the operand
text it predicts, and a label. -/
structure Row where
  /-- Grass's encoding, as lowercase hex. -/
  bytes : String
  /-- The absolute target NDISASM should print when disassembling at origin 0:
  the instruction's length plus its displacement, modulo 2^64. -/
  expectedTarget : BitVec 64
  /-- The disassembly text Grass predicts, normalised: lowercase, no spaces, and
  no operand-size or `near` keywords.

  Without this the differential was blind to the destination register. A
  reviewer stripped `REX.W` from all sixteen `lea` rows — turning
  `lea rax,[rel …]` into `lea eax,[rel …]`, a different instruction — and the
  tool still reported 19 agree, because the expected target and NDISASM's are
  both functions of the same instruction length and move together. Replacing
  every row with identical bytes also passed. Comparing the operand text is what
  makes the register field visible. -/
  expectedText : String
  /-- What the row is, for the report. -/
  label : String

/-- Build a row from an encoding, computing the expected target from the
instruction's own length rather than from a constant.

The arithmetic is `BitVec 64`, not `Nat`. A RIP displacement is **signed** and
the target wraps: with `disp = 0x80000000` a `Nat` sum predicts `0x80000007`
where the processor and NDISASM both give `0xFFFFFFFF80000007`, and with
`disp = -4` the `Nat` version is not representable at all. The corpus uses one
positive displacement today, so this was latent — and the first negative row
would have produced a spurious finding against Grass rather than against the
helper. -/
def rowOf (label : String) (operands : String) (e : InsnEncoding) : Row :=
  let bs := e.toBytes
  let target : BitVec 64 :=
    BitVec.ofNat 64 bs.length + BitVec.signExtend 64 disp
  { bytes := hexBytes bs
    expectedTarget := target
    expectedText := operands ++ "[rel0x" ++ hexTrim target ++ "]"
    label := label }

/-- `lea <dst>, [rip + disp]` for every destination register.

Covers `REX.R` on the RIP form, where the address supplies no extension bits of
its own, so the prefix tests only the `reg` field — and, now that the operand
text is compared, actually distinguishes the sixteen rows from each other. -/
def leaRows : List Row :=
  Gpr.all.filterMap fun d =>
    (leaR64 d (.ripRelative disp)).map fun e =>
      rowOf ("lea " ++ nasmName d ++ ", [rip+disp]") ("lea" ++ nasmName d ++ ",") e

/-- `call qword ptr [rip + disp]` — the import-call form, `FF /2` with no
REX. -/
def callRow : List Row :=
  (callMem64 (.ripRelative disp)).toList.map
    (rowOf "call qword [rip+disp]" "call")

/--
`mov dword ptr [rip + disp], imm32`.

The row that matters most. Its `imm32` follows the displacement, so the
instruction end is four bytes past the displacement field, and an encoder that
resolved RIP against the end of the displacement would be wrong here and right
everywhere else in this corpus.
-/
def movRow : List Row :=
  (movMem32Imm32 (.ripRelative disp) immValue).toList.map
    (rowOf "mov dword [rip+disp], imm32" "mov")

/-- `mov qword ptr [rip + disp], imm32` — the same, with `REX.W`, which is the
only place `movMem64Imm32` is exercised at all. -/
def movQwordRow : List Row :=
  (movMem64Imm32 (.ripRelative disp) immValue).toList.map
    (rowOf "mov qword [rip+disp], imm32" "mov")

/-- The whole RIP corpus. -/
def corpus : List Row := leaRows ++ callRow ++ movRow ++ movQwordRow

end Grass.Tests.ISA.X86.Rip

/-- Print the RIP corpus as
`bytes<TAB>expectedTarget<TAB>expectedText<TAB>label` lines, with the target in
lowercase hex without leading zeros, matching how NDISASM prints it. -/
def main : IO Unit := do
  for r in Grass.Tests.ISA.X86.Rip.corpus do
    IO.println (r.bytes ++ "\t" ++
      Grass.Tests.ISA.X86.Corpus.hexTrim r.expectedTarget ++ "\t" ++
      r.expectedText ++ "\t" ++ r.label)
