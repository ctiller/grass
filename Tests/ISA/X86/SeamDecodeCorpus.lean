import Tests.ISA.X86.CorpusCommon
import Grass.ISA.X86.Target.Encode

/-!
# Seam decode/encode corpus

`Tests/ISA/X86/NasmCorpus.lean` and `Tests/ISA/X86/RipCorpus.lean` are labeled
by NASM source text and NDISASM-predicted output, but the differential that
once fed that text to NASM/NDISASM was removed on 2026-09-08. What remains is
compared against `Grass.ISA.X86.Decode.decodeInsn` and
`Grass.ISA.X86.Encoding`/`Bytes` — the legacy tier `docs/TARGET_SEAMS.md`
retires — never against `Grass.ISA.X86.Target.Encode`'s `Instr`/`encode`/
`decode`, which is what every platform (`Grass.ISA.X86.isa`) is actually wired
to. This file is the re-pointing: it takes each NASM/NDISASM corpus row's
*instruction*, and checks it against the seam wherever the seam can express it
at all.

This file cannot simply `import` `Tests/ISA/X86/NasmCorpus.lean` and
`Tests/ISA/X86/RipCorpus.lean`: both declare a top-level `main`
(`lake env lean --run` looks for it there), and Lean rejects two `main`s in
one environment. Every row shape below is reconstructed instead, using the
exact same generators (`Grass.ISA.X86.leaR64`/`callMem64`/`movMem32Imm32`/
`movMem64Imm32`, `Tests/ISA/X86/CorpusCommon.lean`'s `disp`/`immValue`, and
the same `imm64Value` those files use) — this is deliberately *not* a second,
independently-invented population, so a change to either source stays visible
here as a `lake build` failure if the shapes ever drift apart, rather than as
a silent miscount.

## What the seam cannot express yet

`Grass/ISA/X86/Target/Encode.lean`'s `Instr` has **no memory-operand
constructor of any kind**: no `lea`, no indirect `call` through memory, no
store to memory. Every row built over a `Grass.ISA.X86.MemOperand` —
register-relative, base+index+scale, absolute, or RIP-relative — is therefore
unsupported *by construction*, not by omission here. `Grass/ISA/X86/Target/
Encode.lean`'s own module docstring says memory addressing is "being extended
concurrently with memory-operand families", so this bucket is expected to
shrink; today it is the entire corpus except the opcode-embedded-register
immediate MOV forms.

Those immediate MOV rows — `mov r32, imm32` and `mov r64, imm64` — carry no
memory operand at all, and are checked below: `Grass.ISA.X86.Target.decode` on
the bytes `Grass.ISA.X86.movRegImm32`/`movRegImm64` produce (the same bytes
`Tests/ISA/X86/NasmCorpus.lean` labels with NASM source text) must recover the
seam's own `Instr.movRI32`/`Instr.movRI64`, and `Grass.ISA.X86.Target.encode`
on that `Instr` must reproduce exactly those bytes.

## Places NASM has a legal alternate encoding

The task of re-pointing this corpus is also the task of naming every place a
real assembler could legally have chosen different bytes than the ones being
compared, so that agreement here is not an accident of only ever trying one
encoding:

- **`mov r32, imm32`** has a second legal encoding, `C7 /0 id`
  (`mov r/m32, imm32` through ModR/M, register-direct) — one byte longer.
  NASM, `Grass.ISA.X86.movRegImm32` and `Grass.ISA.X86.Target.Instr.movRI32`
  all choose the shorter opcode-embedded `B8+rd id` form, so they agree; a
  seam that emitted `C7 /0` would still be a correct assembler, just not the
  one this corpus's bytes were generated from.
- **`mov r64, imm64`** has a second legal encoding, `REX.W C7 /0 id`, with the
  immediate sign-extended from 32 bits — three bytes shorter. It cannot
  represent `imm64Value` below, which — matching
  `Tests/ISA/X86/NasmCorpus.lean` — was deliberately chosen not to fit in 32
  bits, so NASM is forced into the same full-immediate `REX.W B8+rd io` form
  the seam always emits. A smaller immediate would make this a real,
  undocumented divergence rather than an agreement, which is why the corpus
  never tests one here.
- Every RIP-relative, base-relative or absolute memory row NASM or NDISASM
  would also pick a specific displacement encoding for (`disp8` vs `disp32`,
  a base-register-implied ModR/M vs a SIB byte) is moot here: those rows are
  entirely unsupported by the seam today (see above), so no byte comparison is
  made for them at all, and none is claimed.

## Honesty

Every NASM/NDISASM row is accounted for exactly once, either in
`checkedRows` (compared byte-for-byte and instruction-for-instruction against
the seam) or in `unsupportedBuckets` (counted by mnemonic, not dropped). `main`
asserts the two totals add up to the full reconstructed population, so a row
that is neither checked nor bucketed fails loudly instead of silently
vanishing.
-/

namespace Grass.Tests.ISA.X86.SeamDecode

open Grass.ISA.X86
open Grass.ISA.X86.Target (Instr encode decode toU8)
open Grass.Tests.ISA.X86.Corpus (hexBytes immValue hex32 hex64 nasmName nasmName32 disp)

/-- Same value, same reasoning, as `Tests/ISA/X86/NasmCorpus.lean`'s
`imm64Value`: every byte distinct, top byte nonzero, and too large for 32
bits, so NASM cannot legally shorten this `mov r64, imm64` to the sign-extended
32-bit-immediate form. -/
def imm64Value : BitVec 64 := 0x89abcdef01234567

/-! ## Rows the seam can express -/

/-- One row the seam can express: a human-readable label (the NASM source
text this row is anchored to), the bytes `Grass.ISA.X86.Bytes`'s legacy
encoder produces for it, the seam `Instr` it should decode to, and whether
`decode`/`encode` agree with those bytes. -/
structure CheckedRow where
  /-- The NASM source line this row is anchored to. -/
  label : String
  /-- The legacy encoder's bytes for this row -- what `Tests/ISA/X86/NasmCorpus.lean`
  would hand to NASM. -/
  bytes : List UInt8
  /-- The seam instruction this row denotes. -/
  instr : Instr
  /-- Whether `Grass.ISA.X86.Target.decode` on `bytes` recovers exactly
  `(instr, bytes.length)`. -/
  decodeOk : Bool
  /-- Whether `Grass.ISA.X86.Target.encode instr` reproduces `bytes` exactly. -/
  encodeOk : Bool

/-- Build one checked row. -/
def checkRow (label : String) (instr : Instr) (bytes : List UInt8) : CheckedRow :=
  { label := label, bytes := bytes, instr := instr
    decodeOk := decide (decode bytes = some (instr, bytes.length))
    encodeOk := decide (encode instr = bytes) }

/-- `mov r32, imm32` (`B8+rd id`) over every register. -/
def movRI32Rows : List CheckedRow :=
  Gpr.all.map fun r =>
    checkRow ("mov " ++ nasmName32 r ++ ", " ++ hex32 immValue)
      (Instr.movRI32 r immValue) ((movRegImm32 r immValue).toBytes.map toU8)

/-- `mov r64, imm64` (`REX.W B8+rd io`) over every register. -/
def movRI64Rows : List CheckedRow :=
  Gpr.all.map fun r =>
    checkRow ("mov " ++ nasmName r ++ ", " ++ hex64 imm64Value)
      (Instr.movRI64 r imm64Value) ((movRegImm64 r imm64Value).toBytes.map toU8)

/-- Every row the seam can express today. -/
def checkedRows : List CheckedRow := movRI32Rows ++ movRI64Rows

/-! ## Rows the seam cannot express, reconstructed only to count them

Each list below reconstructs, by row count only, one group from
`Tests/ISA/X86/NasmCorpus.lean` or `Tests/ISA/X86/RipCorpus.lean`, using their
own generators and constants so a change to either population is visible here
as a build failure rather than a stale count. -/

def scales : List Scale := [.s1, .s2, .s4, .s8]

def nasmBaseRows : List InsnEncoding := Gpr.all.filterMap fun b => leaR64 .rax (.base b disp)
def nasmDestRows : List InsnEncoding := Gpr.all.filterMap fun d => leaR64 d (.base .rbx disp)
def nasmBaseIndexRows : List InsnEncoding :=
  Gpr.all.flatMap fun b => Gpr.all.flatMap fun idx =>
    scales.filterMap fun s => leaR64 .rax (.baseIndex b idx s disp)
def nasmIndexOnlyRows : List InsnEncoding :=
  Gpr.all.flatMap fun idx => scales.filterMap fun s => leaR64 .rax (.indexOnly idx s disp)
def nasmAbsoluteRows : List InsnEncoding := (leaR64 .rax (.absolute disp)).toList
def nasmCallRows : List InsnEncoding := Gpr.all.filterMap fun b => callMem64 (.base b disp)
def nasmMovRows : List InsnEncoding :=
  Gpr.all.filterMap fun b => movMem32Imm32 (.base b disp) immValue
def ripLeaRows : List InsnEncoding := Gpr.all.filterMap fun d => leaR64 d (.ripRelative disp)
def ripCallRow : List InsnEncoding := (callMem64 (.ripRelative disp)).toList
def ripMovRow : List InsnEncoding := (movMem32Imm32 (.ripRelative disp) immValue).toList
def ripMovQwordRow : List InsnEncoding := (movMem64Imm32 (.ripRelative disp) immValue).toList

/-- One mnemonic-labeled bucket of NASM/NDISASM rows the seam cannot express
at all, and how many corpus rows fall in it. -/
structure UnsupportedBucket where
  /-- The instruction shape, named precisely enough to tell rows apart. -/
  mnemonic : String
  /-- How many corpus rows have this shape. -/
  count : Nat

/-- Every NASM/NDISASM row not in `checkedRows`, bucketed by mnemonic. Every
one of them carries a `Grass.ISA.X86.MemOperand`, which the seam has no
`Instr` constructor for at all. -/
def unsupportedBuckets : List UnsupportedBucket :=
  [ { mnemonic := "lea r64, [base+disp32] (base register swept)", count := nasmBaseRows.length }
  , { mnemonic := "lea <dst>, [rbx+disp32] (destination register swept)"
      count := nasmDestRows.length }
  , { mnemonic := "lea rax, [base+index*scale+disp32]", count := nasmBaseIndexRows.length }
  , { mnemonic := "lea rax, [index*scale+disp32] (SIB, no base)"
      count := nasmIndexOnlyRows.length }
  , { mnemonic := "lea rax, [disp32] (SIB, absolute)", count := nasmAbsoluteRows.length }
  , { mnemonic := "call qword [base+disp32]", count := nasmCallRows.length }
  , { mnemonic := "mov dword [base+disp32], imm32", count := nasmMovRows.length }
  , { mnemonic := "lea <dst>, [rip+disp32]", count := ripLeaRows.length }
  , { mnemonic := "call qword [rip+disp32]", count := ripCallRow.length }
  , { mnemonic := "mov dword [rip+disp32], imm32", count := ripMovRow.length }
  , { mnemonic := "mov qword [rip+disp32], imm32", count := ripMovQwordRow.length } ]

/-- Total unsupported rows across every bucket. -/
def totalUnsupported : Nat := (unsupportedBuckets.map UnsupportedBucket.count).foldl (· + ·) 0

/-- The full NASM/NDISASM population `checkedRows` and `unsupportedBuckets`
must jointly account for: `Tests/ISA/X86/NasmCorpus.lean`'s `corpus` is
`baseRows ++ destRows ++ baseIndexRows ++ indexOnlyRows ++ absoluteRows ++
callRows ++ movRows ++ movRegImm32Rows ++ movRegImm64Rows`, and
`Tests/ISA/X86/RipCorpus.lean`'s is `leaRows ++ callRow ++ movRow ++
movQwordRow`. -/
def totalCorpus : Nat :=
  nasmBaseRows.length + nasmDestRows.length + nasmBaseIndexRows.length +
    nasmIndexOnlyRows.length + nasmAbsoluteRows.length + nasmCallRows.length +
    nasmMovRows.length + movRI32Rows.length + movRI64Rows.length +
    ripLeaRows.length + ripCallRow.length + ripMovRow.length + ripMovQwordRow.length

/-- The report `main` prints and acts on. -/
def report : IO Unit := do
  let rows := checkedRows
  let mismatches := rows.filter fun r => !r.decodeOk || !r.encodeOk
  IO.println "== Seam decode/encode corpus (Tests/ISA/X86/SeamDecodeCorpus.lean) =="
  IO.println s!"NASM/NDISASM corpus rows total: {totalCorpus}"
  IO.println s!"  checked against the seam:     {rows.length}"
  IO.println s!"  unsupported (no seam Instr):  {totalUnsupported}"
  IO.println ""
  IO.println "-- documented alternate legal encodings (not failures) --"
  IO.println "mov r32, imm32: NASM/Grass both choose the shorter B8+rd id form over C7 /0 id"
  IO.println "mov r64, imm64: imm64Value does not fit in 32 bits, forcing REX.W B8+rd io \
    over the shorter REX.W C7 /0 id sign-extended form"
  IO.println ""
  IO.println "-- unsupported buckets, by mnemonic --"
  for b in unsupportedBuckets do
    IO.println s!"  {b.count}  {b.mnemonic}"
  IO.println ""
  if mismatches.isEmpty then
    IO.println s!"checked rows: {rows.length} agree, 0 mismatches"
  else
    IO.println s!"checked rows: {rows.length - mismatches.length} agree, \
      {mismatches.length} MISMATCH"
    for r in mismatches do
      IO.println s!"MISMATCH {r.label}"
      IO.println s!"  bytes:        {hexBytes (r.bytes.map UInt8.toBitVec)}"
      IO.println s!"  seam instr:   {reprStr r.instr}"
      IO.println s!"  seam decode:  {reprStr (decode r.bytes)}"
      IO.println s!"  seam encode:  {hexBytes ((encode r.instr).map UInt8.toBitVec)}"
  if rows.length + totalUnsupported != totalCorpus then
    IO.println s!"ACCOUNTING ERROR: checked ({rows.length}) + unsupported \
      ({totalUnsupported}) = {rows.length + totalUnsupported} but the corpus has \
      {totalCorpus} rows -- some row is neither checked nor bucketed"
    IO.Process.exit 1
  if !mismatches.isEmpty then
    IO.Process.exit 1

end Grass.Tests.ISA.X86.SeamDecode

/-- Top level rather than in the namespace because `lake env lean --run` looks
for `main` there. -/
def main : IO Unit := Grass.Tests.ISA.X86.SeamDecode.report
