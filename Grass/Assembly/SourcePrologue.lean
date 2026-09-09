import Grass.ABI.Win64.UnwindBytes
import Grass.Assembly.ByteLayout
import Grass.Assembly.FrameAllocation
import Grass.Assembly.SourceFrame
import Grass.ISA.X86.BasicInstructions

/-! Generate only the saved-register pushes, stack allocation, and corresponding
Win64 unwind layout. Body initialization, relinking, and physical stack
semantics remain outside this module. -/
namespace Grass.Assembly.SourcePrologue

open Grass.ABI.Win64 Grass.ISA.X86 Grass.ISA.X86.BasicInstructions Grass.Std.Logical
open Grass.Assembly.ByteLayout

def allocationOp? (bytes : Nat) : Option UnwindOp :=
  if _h : (UnwindOp.allocSmall bytes).Encodable then some (.allocSmall bytes)
  else if _h : (UnwindOp.allocLarge bytes).Encodable then some (.allocLarge bytes)
  else none

def instructions (frame : SourceFrame.Result) (allocation : FrameAllocation.Resolved) :
    List InsnEncoding :=
  frame.saved.registers.map BasicInstructions.push ++ [allocation.encoding]

def operations (frame : SourceFrame.Result) (allocationOp : UnwindOp) : List UnwindOp :=
  frame.saved.registers.map .pushNonvolatile ++ [allocationOp]

def placed (encodings : List InsnEncoding) (ops : List UnwindOp) : List PlacedOp :=
  ops.zipIdx.map fun (op, index) =>
    ⟨op, BitVec.ofNat 8 (offset (sizes encodings) (index + 1))⟩

def metadata (encodings : List InsnEncoding) (ops : List UnwindOp) : Layout :=
  ⟨placed encodings ops, BitVec.ofNat 8 (sizes encodings).sum⟩

def expectedOffsets (encodings : List InsnEncoding) : List Byte :=
  (List.range encodings.length).map fun index =>
    BitVec.ofNat 8 (offset (sizes encodings) (index + 1))

structure Result where
  private mk ::
  frame : SourceFrame.Result
  allocation : FrameAllocation.Resolved
  allocationOp : UnwindOp
  generated : List InsnEncoding
  unwindOps : List UnwindOp
  unwindLayout : Layout
  remainder : List X86ControlFlow.CodeItem
  allocationExact : FrameAllocation.resolve? frame.layout = some allocation
  allocationOpExact : allocationOp? frame.layout.callAllocationBytes = some allocationOp
  generatedExact : generated = instructions frame allocation
  unwindOpsExact : unwindOps = operations frame allocationOp
  remainderExact : remainder = frame.saved.rest
  metadataExact : unwindLayout = metadata generated unwindOps
  offsetsExact : unwindLayout.offsets = expectedOffsets generated
  prologueFitsByte : (sizes generated).sum ≤ 255
  offsetNatsExact : unwindLayout.offsets.map BitVec.toNat =
    (List.range generated.length).map fun index => offset (sizes generated) (index + 1)
  sizeOfPrologExact : unwindLayout.sizeOfProlog.toNat =
    (ByteLayout.emitted generated).length
  metadataWellFormed : unwindLayout.WellFormed
  stackDeltaExact : unwindLayout.prologue.stackDelta = frame.layout.totalFrameBytes

def generate? (frame : SourceFrame.Result) : Option Result := do
  match ha : FrameAllocation.resolve? frame.layout with
  | none => none
  | some allocation =>
    match ho : allocationOp? frame.layout.callAllocationBytes with
    | none => none
    | some allocationOp =>
      let generated := instructions frame allocation
      let unwindOps := operations frame allocationOp
      let unwindLayout := metadata generated unwindOps
      if hoff : unwindLayout.offsets = expectedOffsets generated then
        if hb : (sizes generated).sum ≤ 255 then
          if hn : unwindLayout.offsets.map BitVec.toNat =
              (List.range generated.length).map fun index => offset (sizes generated) (index + 1) then
            if hz : unwindLayout.sizeOfProlog.toNat = (ByteLayout.emitted generated).length then
              if hw : unwindLayout.WellFormed then
                if hd : unwindLayout.prologue.stackDelta = frame.layout.totalFrameBytes then
                  some ⟨frame, allocation, allocationOp, generated, unwindOps, unwindLayout,
                    frame.saved.rest, ha, ho, rfl, rfl, rfl, rfl, hoff, hb, hn, hz, hw, hd⟩
                else none
              else none
            else none
          else none
        else none
      else none

theorem generate?_frame {frame : SourceFrame.Result} {result : Result}
    (success : generate? frame = some result) : result.frame = frame := by
  unfold generate? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  dsimp only at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  rfl

theorem Result.generated_shape (result : Result) :
    result.generated = result.frame.saved.registers.map BasicInstructions.push ++
      [result.allocation.encoding] := result.generatedExact

theorem Result.code_offsets_from_instruction_ends (result : Result) :
    result.unwindLayout.offsets =
      (List.range result.generated.length).map fun index =>
        BitVec.ofNat 8 (offset (sizes result.generated) (index + 1)) :=
  result.offsetsExact

theorem Result.code_offset_naturals (result : Result) :
    result.unwindLayout.offsets.map BitVec.toNat =
      (List.range result.generated.length).map fun index =>
        offset (sizes result.generated) (index + 1) := result.offsetNatsExact

theorem Result.stored_prologue_size (result : Result) :
    result.unwindLayout.sizeOfProlog.toNat =
      (ByteLayout.emitted result.generated).length := result.sizeOfPrologExact

theorem Result.every_instruction_decodes (result : Result) (encoding : InsnEncoding)
    (member : encoding ∈ result.generated) (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest) := by
  rw [result.generatedExact] at member
  rcases List.mem_append.mp member with pushed | allocated
  · obtain ⟨reg, _, rfl⟩ := List.mem_map.mp pushed
    exact push_decodes reg rest
  · simp only [List.mem_singleton] at allocated
    subst encoding
    exact FrameAllocation.encoding_decodes result.allocation rest

theorem Result.emitted_length (result : Result) :
    (ByteLayout.emitted result.generated).length = (sizes result.generated).sum :=
  ByteLayout.emitted_length result.generated

end Grass.Assembly.SourcePrologue
