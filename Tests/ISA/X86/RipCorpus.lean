import Tests.ISA.X86.CorpusCommon

/-!
# RIP-relative disassembly corpus

The RIP-relative form is the one this profile cannot check against an
assembler, and it is the form Spike 1 depends on most: every import call and the
payload address go through `mod=00, rm=101`. `Tools/x86-nasm-differential.py`
skips it because NASM computes a RIP displacement from a target address and an
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

`Tools/x86-ndisasm-differential.py` consumes this and checks each row.
-/

namespace Grass.Tests.ISA.X86.Rip

open Grass.Std.Logical Grass.ISA.X86 Grass.Tests.ISA.X86.Corpus

/-- One RIP-relative row: Grass's bytes, its own computed target, and a label. -/
structure Row where
  /-- Grass's encoding, as lowercase hex. -/
  bytes : String
  /-- The absolute target NDISASM should print when disassembling at origin 0:
  the instruction's length plus its displacement. -/
  expectedTarget : Nat
  /-- What the row is, for the report. -/
  label : String

/-- Build a row from an encoding, computing the expected target from the
instruction's own length rather than from a constant. -/
def rowOf (label : String) (e : InsnEncoding) : Row :=
  let bs := e.toBytes
  { bytes := hexBytes bs
    expectedTarget := bs.length + disp.toNat
    label := label }

/-- `lea <dst>, [rip + disp]` for every destination register.

Covers `REX.R` on the RIP form, where the address supplies no extension bits of
its own, so the prefix is testing only the `reg` field. -/
def leaRows : List Row :=
  Gpr.all.filterMap fun d =>
    (leaR64 d (.ripRelative disp)).map fun e =>
      rowOf ("lea " ++ nasmName d ++ ", [rip+disp]") e

/-- `call qword ptr [rip + disp]` — the import-call form, `FF /2` with no
REX. -/
def callRow : List Row :=
  (callMem64 (.ripRelative disp)).toList.map (rowOf "call qword [rip+disp]")

/--
`mov dword ptr [rip + disp], imm32`.

The row that matters most. Its `imm32` follows the displacement, so the
instruction end is four bytes past the displacement field, and an encoder that
resolved RIP against the end of the displacement would be wrong here and right
everywhere else in this corpus.
-/
def movRow : List Row :=
  (movMem32Imm32 (.ripRelative disp) immValue).toList.map
    (rowOf "mov dword [rip+disp], imm32")

/-- `mov qword ptr [rip + disp], imm32` — the same, with `REX.W`, which is the
only place `movMem64Imm32` is exercised at all. -/
def movQwordRow : List Row :=
  (movMem64Imm32 (.ripRelative disp) immValue).toList.map
    (rowOf "mov qword [rip+disp], imm32")

/-- The whole RIP corpus. -/
def corpus : List Row := leaRows ++ callRow ++ movRow ++ movQwordRow

end Grass.Tests.ISA.X86.Rip

/-- Print the RIP corpus as `bytes<TAB>expectedTarget<TAB>label` lines. -/
def main : IO Unit := do
  for r in Grass.Tests.ISA.X86.Rip.corpus do
    IO.println (r.bytes ++ "\t" ++ toString r.expectedTarget ++ "\t" ++ r.label)
