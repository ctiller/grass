import Grass.Assembly.SourceFrame
import Grass.Assembly.LocalAddress

/-! Typed UInt32 local loads from the frame's authoritative slot environment.
`Result.encoding_decodes` checks the emitted encoding; instruction execution and
the correspondence of physical RSP to the frame remain separate obligations. -/
namespace Grass.Assembly.FrameLoad

open Grass.ISA.X86 X86ControlFlow

structure Result where
  private mk ::
  frame : SourceFrame.Result
  item : CodeItem
  destination : Gpr
  slot : String
  address : LocalAddress.Result
  encoding : InsnEncoding
  member : item ∈ frame.program.collected.code
  instructionExact : item.instruction =
    ⟨.mov, [.register ⟨destination, .w32⟩, .symbol slot]⟩
  addressExact : LocalAddress.resolve? frame.layout address.rootOffset
    (SourceStore.slotEnv frame.slots) slot 4 = some address
  encodingExact : BasicInstructions.movReg32Mem destination address.operand = some encoding

def resolve? (frame : SourceFrame.Result) (rootOffset : Nat) (item : CodeItem) : Option Result :=
  if member : item ∈ frame.program.collected.code then
    match instruction : item.instruction with
    | ⟨.mov, [.register ⟨destination, .w32⟩, .symbol slot]⟩ =>
      match addressEq : LocalAddress.resolve? frame.layout rootOffset
          (SourceStore.slotEnv frame.slots) slot 4 with
      | none => none
      | some address =>
        match encodingEq : BasicInstructions.movReg32Mem destination address.operand with
        | none => none
        | some encoding =>
          some ⟨frame, item, destination, slot, address, encoding, member, instruction,
            by rw [(LocalAddress.resolve?_exact addressEq).2.1]; exact addressEq,
            encodingEq⟩
    | _ => none
  else none

theorem resolve?_source {frame : SourceFrame.Result} {rootOffset : Nat} {item : CodeItem}
    {result : Result} (success : resolve? frame rootOffset item = some result) :
    result.frame = frame ∧ result.item = item ∧ result.address.rootOffset = rootOffset := by
  unfold resolve? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  rename_i address addressEq
  split at success <;> try contradiction
  cases success
  exact ⟨rfl, rfl, (LocalAddress.resolve?_exact addressEq).2.1⟩

theorem Result.range_in_frame (result : Result) :
    (result.frame.layout.frameRange.shift result.address.rootOffset).Contains result.address.range := by
  have exactAddress := LocalAddress.resolve?_exact result.addressExact
  rw [← exactAddress.1]
  exact result.address.range_in_frame

theorem Result.load_width (result : Result) : result.address.width = 4 :=
  (LocalAddress.resolve?_exact result.addressExact).2.2.2.1

theorem Result.encoding_decodes (result : Result) (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (result.encoding.toBytes ++ rest) = .ok (result.encoding, rest) :=
  BasicInstructions.movReg32Mem_decodes result.encodingExact rest

end Grass.Assembly.FrameLoad
