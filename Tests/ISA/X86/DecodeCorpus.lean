import Grass.ISA.X86.Decode
import Tests.ISA.X86.CorpusCommon

/-!
# Decoder corpus, for differential checking of instruction *length* against NDISASM

`Tests/ISA/X86/NasmCorpus.lean` and `Tests/ISA/X86/RipCorpus.lean` check the
encoder. Nothing checked the decoder, and a reviewer showed exactly what that
cost: five separate mutations of `opcodeTable` and `dispKindFor` survived
`lake build` *and* both existing differentials.

The reason is structural, not an oversight. `MatchesSpec` requires the record
and the table row to agree with each other; neither is required to agree with
the ISA. `dispKindFor` is the single definition behind both
`InsnEncoding.WellFormed` and `decodeOperands`, so changing it keeps encoder and
decoder consistent and `decodeInsn_toBytes` still compiles. And the two encoder
differentials only ever feed NASM bytes the encoder chose to emit, which never
include `mod=01`, and never a `mod=00` SIB with a base other than `101` -- so
those branches of `dispKindFor` were unreachable from every check in the
repository.

## What is compared

Length, and only length. That is the property a wrong table or a wrong
displacement rule destroys, and it is the one that matters most: a decoder that
gets a field wrong reports one bad instruction, while a decoder that gets a
length wrong resumes inside the next instruction and every instruction after it
is garbage. It is also the property NDISASM reports unambiguously, as the offset
of the following instruction.

Each row is a fixed-width window: the instruction's leading bytes, then `0x90`
padding out to `windowBytes`. Grass decodes the window and reports how many
bytes it consumed; NDISASM disassembles the same window and its second
instruction boundary is the answer. Padding with `NOP` rather than zeros keeps
the filler decodable, so a length disagreement shows up as a boundary
disagreement rather than as NDISASM giving up.

## Coverage

Every row of `opcodeTable`, under four REX prefixes: absent, `REX.W`, `REX.B`
and `REX.X`. `REX.W` is there because it changes the immediate size for
`B8+rd`, which is the bug this corpus was written after; `REX.X` because it is
the bit that makes `R12` usable as an index.

For a row taking a ModR/M byte, all 256 ModR/M values, plus a full sweep of all
256 SIB bytes for one representative ModR/M in each of `mod=00`, `mod=01` and
`mod=10` with `rm=100`. The full ModR/M × SIB cross product would be about six
times larger and add nothing: the displacement rule depends on `mod`, on `rm`,
and on the SIB `base` field, and those three sweeps cover each.

## What this does not check

Validity. NDISASM rejects encodings this decoder accepts -- `8D` with `mod=11`
is `#UD`, and several `/digit` values are unassigned -- and those rows are
reported separately as `oracle refused` rather than counted as agreement.
`decodeInsn` is a length-and-fields parser, not a validity checker, and
`DecodeError` has no case for "that opcode does not take that extension".
-/

namespace Grass.Tests.ISA.X86.DecodeC

open Grass.ISA.X86 Grass.Std.Logical
open Grass.Tests.ISA.X86.Corpus (hexBytes hexByte)

/-- Each window is this many bytes: the instruction, then `NOP` padding.

Twenty-four is comfortably above the longest encoding this profile can produce
(`REX` + `B8+rd` + `imm64` is ten; `REX` + opcode + ModR/M + SIB + `disp32` +
`imm32` is twelve), so the padding is never consumed by a correct decode and a
badly wrong one still stays inside its own window. -/
def windowBytes : Nat := 24

/-- The REX prefixes swept, `none` first. -/
def rexBytes : List (Option Byte) :=
  [none, some 0x48, some 0x41, some 0x42]

/-- A label for a prefix, for the tool's report. -/
def rexLabel : Option Byte → String
  | none => "norex"
  | some b => "rex" ++ hexByte b

/-- Pad a byte list out to `windowBytes` with `NOP`. -/
def window (core : ByteSeq) : ByteSeq :=
  core ++ List.replicate (windowBytes - core.length) 0x90

/-- How many bytes `decodeInsn` consumes from a window, or `0` if it refuses.

A refusal is itself a finding here, because every window is built from an opcode
the table contains and is padded to a length no encoding needs. -/
def grassLength (bs : ByteSeq) : Nat :=
  match decodeInsn bs with
  | .ok (_, rest) => bs.length - rest.length
  | .error _ => 0

/-- The opcode bytes for a row, without operands. -/
def coreOf (s : OpcodeSpec) (rex : Option Byte) : ByteSeq :=
  (match rex with | none => [] | some b => [b]) ++
    (if s.escape then [InsnEncoding.escapeByte] else []) ++ [s.opcode]

/-- A corpus row. -/
structure Row where
  /-- The window's bytes, lowercase hex. -/
  bytes : String
  /-- The length `decodeInsn` reports. -/
  length : Nat
  /-- A label naming the row, prefix and operand bytes. -/
  label : String

/-- Build one row from a fully-formed core. -/
def rowOf (label : String) (core : ByteSeq) : Row :=
  let w := window core
  { bytes := hexBytes w, length := grassLength w, label := label }

/-- Whether this ModR/M byte selects a SIB byte. -/
def modrmNeedsSib (b : Byte) : Bool :=
  let m := ModRm.ofByte b
  m.rm == ModRm.rmSelectsSib && m.mod != ModRm.modRegisterDirect

/-- The 256 ModR/M sweeps for one row and prefix, with a fixed SIB where the
ModR/M byte calls for one. `0x24` is `scale=00 index=100 base=100`: no index,
`RSP` as base, which is the SIB an encoder emits most often. -/
def modrmRows (s : OpcodeSpec) (rex : Option Byte) : List Row :=
  (List.range 256).map fun i =>
    let b : Byte := BitVec.ofNat 8 i
    let core := coreOf s rex ++ [b] ++ (if modrmNeedsSib b then [0x24] else [])
    rowOf (s.mnemonic ++ "/" ++ rexLabel rex ++ "/modrm" ++ hexByte b) core

/-- The 256 SIB sweeps for one ModR/M byte. -/
def sibRows (s : OpcodeSpec) (rex : Option Byte) (modrm : Byte) : List Row :=
  (List.range 256).map fun i =>
    let sib : Byte := BitVec.ofNat 8 i
    let core := coreOf s rex ++ [modrm, sib]
    rowOf (s.mnemonic ++ "/" ++ rexLabel rex ++ "/modrm" ++ hexByte modrm ++
      "/sib" ++ hexByte sib) core

/-- The representative ModR/M bytes whose SIB field is swept: `rm=100` with
`reg=000`, in each of the three memory `mod` values. -/
def sibSweepModrms : List Byte := [0x04, 0x44, 0x84]

/-- Every row for one opcode and one prefix. -/
def rowsFor (s : OpcodeSpec) (rex : Option Byte) : List Row :=
  if s.hasModrm then
    modrmRows s rex ++ (sibSweepModrms.flatMap fun m => sibRows s rex m)
  else
    [rowOf (s.mnemonic ++ "/" ++ rexLabel rex) (coreOf s rex)]

/-- The whole corpus. -/
def corpus : List Row :=
  opcodeTable.flatMap fun s => rexBytes.flatMap fun r => rowsFor s r

end Grass.Tests.ISA.X86.DecodeC

/-- Print the corpus as tab-separated `bytes<TAB>length<TAB>label` lines.

Top level rather than in the namespace because `lake env lean --run` looks for
`main` there. -/
def main : IO Unit := do
  for r in Grass.Tests.ISA.X86.DecodeC.corpus do
    IO.println (r.bytes ++ "\t" ++ toString r.length ++ "\t" ++ r.label)
