import Grass.Assembly.SourcePrologue
import Tests.Assembly.SourceLiteral
import Tests.ISA.X86.CorpusCommon

/-!
# Bounded native stack corpus

This executable emits validation data, never proof authority.  It deliberately
stops at the modeled stack effects needed by the native scratch-stack runner:
`PUSH r64` writes one eight-byte little-endian value while decreasing RSP by
eight, and `SUB rsp, imm` decreases RSP by the resolved positive allocation.
It makes no claim about whole-machine instruction semantics, faults, paging, or
unmodeled state.

The Python runner directly supplies the same register-value pattern as
`Tests.ISA.X86.NativeCorpus.initial`; this module neither imports nor executes
that earlier corpus.  After choosing its scratch address, the adapter computes
its own test-local little-endian PUSH reference from the TSV's register indices.
For `push rsp`, it substitutes the incoming scratch-stack RSP for the placeholder
at register index four.

Rows have six tab-separated fields:

`label`, `bytes`, `rsp_decrease_decimal`, `pushed-register-indices`,
`flags_preserved`, `basis`.

The pushed-register field is in instruction execution order.  It is `-` when
there is no push.  Only the single-instruction, pure PUSH rows say `yes` for
flag preservation; generated prologues and allocation rows leave that field
unspecified (`-`).
-/
namespace Grass.Tests.ISA.X86.NativeStackCorpus

open Grass.ABI.Win64 Grass.Assembly Grass.ISA.X86 Grass.Std.Logical
open Grass.Tests.ISA.X86.Corpus

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

structure Row where
  label : String
  bytes : ByteSeq
  rspDecrease : Nat
  pushedRegisterIndices : List Nat
  flagsPreserved : Bool
  basis : String
deriving DecidableEq

def pushRow (reg : Gpr) : Row :=
  { label := s!"push-{reg.index.val}"
    bytes := Grass.ISA.X86.BasicInstructions.push reg |>.toBytes
    rspDecrease := 8
    pushedRegisterIndices := [reg.index.val]
    flagsPreserved := true
    basis := "BasicInstructions.push+test-local-push-le64" }

def pushRows : List Row := Gpr.all.map pushRow

/-! With one saved register, these real layouts produce the closest allocation
on each side of the signed-i8 boundary: 112 uses `83 /5 ib`, while 128 is the
first layout here to require `81 /5 id`.  Only the allocation encoding is run in
these rows, so their RSP decrease is the layout's call allocation, not its total
frame size. -/
def allocationBoundaryLayout (localBytes : Nat) : CallFrameLayout :=
  { argumentCount := 4
    localBytes := localBytes
    localAlignment := 4
    savedRegisters := [.rbx] }

def allocationRow? (layout : CallFrameLayout) : Option Row := do
  let resolved ← FrameAllocation.resolve? layout
  some
    { label := s!"alloc-{resolved.layout.callAllocationBytes}"
      bytes := resolved.encoding.toBytes
      rspDecrease := resolved.layout.callAllocationBytes
      pushedRegisterIndices := []
      flagsPreserved := false
      basis := "FrameAllocation.resolve?+CallFrameLayout.callAllocationBytes" }

def allocationRows : List Row :=
  [allocationBoundaryLayout 80, allocationBoundaryLayout 96].filterMap allocationRow?

example : (allocationBoundaryLayout 80).callAllocationBytes = 112 := by decide
example : (allocationBoundaryLayout 96).callAllocationBytes = 128 := by decide
example : allocationRows.map Row.rspDecrease = [112, 128] := by decide

def sourcePrologue? (chars : List Char) : Option SourcePrologue.Result := do
  let body ← (SourceInput.extractHelloSourceChars chars).toOption
  let frame ← SourceFrame.derive? body
  SourcePrologue.generate? frame

def sample (saved : List Char) : List Char :=
  (source_chars "def helloSource : MachineSource plan := withStack (value : UInt32 := 0) withCallFrame WriteFile asm_source (statics := statics) {\n") ++
    saved ++ (source_chars "\nud2\n}")

def authored : List Char :=
  include_source_chars "../../../Spikes/1_Hello_World/Program.lean"

def prologueRow? (label : String) (chars : List Char) : Option Row := do
  let result ← sourcePrologue? chars
  some
    { label := "prologue-" ++ label
      bytes := ByteLayout.emitted result.generated
      rspDecrease := result.unwindLayout.prologue.stackDelta
      pushedRegisterIndices := result.frame.saved.registers.map (·.index.val)
      flagsPreserved := false
      basis := "SourceFrame.derive?+SourcePrologue.generate?+unwind.stackDelta" }

/-! Each prologue is emitted exactly once from `Result.generated`.  The authored
Spike 1 source supplies the three-extended-register case; the other public
source builders exercise mixed one/two-byte PUSH encodings and the complete
Win64 nonvolatile GPR set (excluding RSP, which has no unwind description). -/
def prologueRows : List Row :=
  [ prologueRow? "mixed-rbx-r12"
      (sample (source_chars "push rbx\npush r12"))
  , prologueRow? "authored-spike1" authored
  , prologueRow? "all-nonvolatile"
      (sample (source_chars
        "push rbx\npush rbp\npush rsi\npush rdi\npush r12\npush r13\npush r14\npush r15"))
  ].reduceOption

def rows : List Row := pushRows ++ allocationRows ++ prologueRows

def labels (items : List Row) : List String := items.map Row.label
def byteStrings (items : List Row) : List ByteSeq := items.map Row.bytes

def pushedIndicesText (indices : List Nat) : String :=
  if indices.isEmpty then "-" else String.intercalate "," (indices.map toString)

def emit (row : Row) : IO Unit :=
  IO.println (String.intercalate "\t"
    [ row.label
    , hexBytes row.bytes
    , toString row.rspDecrease
    , pushedIndicesText row.pushedRegisterIndices
    , if row.flagsPreserved then "yes" else "-"
    , row.basis ])

/-! Fail closed before emitting any partial corpus.  These executable checks
bound validation data; they are not propositions used as proof authority. -/
def generate : IO Unit := do
  unless rows.length == 21 do
    throw (IO.userError "native stack corpus: incomplete population")
  unless decide (labels rows).Nodup do
    throw (IO.userError "native stack corpus: duplicate label")
  unless decide (byteStrings rows).Nodup do
    throw (IO.userError "native stack corpus: duplicate instruction bytes")
  unless rows.all (fun row => row.bytes.length ≤ 255) do
    throw (IO.userError "native stack corpus: body exceeds 255 bytes")
  unless rows.all (fun row => row.rspDecrease ≤ 8192) do
    throw (IO.userError "native stack corpus: stack decrease exceeds 8192 bytes")
  unless prologueRows.length == 3 &&
      prologueRows.all (fun row => 1 < row.pushedRegisterIndices.length) do
    throw (IO.userError "native stack corpus: generated prologue population is incomplete")
  rows.forM emit

end Grass.Tests.ISA.X86.NativeStackCorpus

def main : IO Unit := Grass.Tests.ISA.X86.NativeStackCorpus.generate
