import Grass.Assembly.SourcePrologue
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SourcePrologue

open Grass.Assembly SourceInput SourcePrologue

def fromChars? (chars : List Char) : Option Result := do
  let body ← (extractHelloSourceChars chars).toOption
  let frame ← SourceFrame.derive? body
  generate? frame

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def view (result : Result) : List Nat × List Nat × Nat × Nat :=
  (result.generated.map Grass.ISA.X86.InsnEncoding.size,
    result.unwindLayout.offsets.map BitVec.toNat,
    result.unwindLayout.prologue.stackDelta,
    result.unwindLayout.sizeOfProlog.toNat)

-- These numbers observe source-derived machine and metadata output; none is an
-- input to the generator.
example : (fromChars? authored).map view = some ([2, 2, 2, 4], [2, 4, 6, 10], 72, 10) := by
  decide +kernel

def sample (saved : List Char) : List Char :=
  (source_chars "def helloSource : MachineSource plan := withStack (value : UInt32 := 0) withCallFrame WriteFile asm_source (statics := statics) {\n") ++
    saved ++ (source_chars "\nud2\n}")

-- Rbx has a one-byte PUSH while r12 needs REX, so every following metadata
-- position is recomputed from the changed encoding.
example : (fromChars? (sample (source_chars "push rbx"))).map view =
    some ([1, 4], [1, 5], 56, 5) := by decide +kernel
example : (fromChars? (sample (source_chars "push r12"))).map view =
    some ([2, 4], [2, 6], 56, 6) := by decide +kernel

-- The unwind allocation selector covers both encodings and refuses values
-- outside either format, including an otherwise-small unaligned amount.
example : allocationOp? 128 = some (.allocSmall 128) := by decide
example : allocationOp? 136 = some (.allocLarge 136) := by decide
example : allocationOp? 524280 = some (.allocLarge 524280) := by decide
example : allocationOp? 524288 = none := by decide
example : allocationOp? 12 = none := by decide

theorem generated_metadata_is_well_formed (result : Result) :
    result.unwindLayout.WellFormed := result.metadataWellFormed

theorem generated_stack_delta_is_the_computed_frame (result : Result) :
    result.unwindLayout.prologue.stackDelta = result.frame.layout.totalFrameBytes :=
  result.stackDeltaExact

end Grass.Tests.Assembly.SourcePrologue
