import Grass.Assembly.SourceFrame
import Grass.Assembly.X86ClosedEncoding
import Grass.ISA.X86.ImmediateArithmetic
import Grass.Platform.Win32.Console

/-! Lower the two named Win32 constants used by the Spike 1 source.  Values
come from the platform model; this module chooses only their x86 representation.
It proves source and decoder correspondence, not register or instruction
execution. -/

namespace Grass.Assembly.Win32Constants

open Grass.ISA.X86 Grass.ISA.X86.BasicInstructions Grass.Platform.Win32
open X86ControlFlow

inductive Constant where
  | stdOutputHandle
  | invalidHandleValue
deriving DecidableEq, Repr

def Constant.value : Constant → BitVec 64
  | .stdOutputHandle => BitVec.setWidth 64 StdHandleId.output.value
  | .invalidHandleValue => GetStdHandleResult.invalidHandleValue

def selectSignedImmediate? (value : BitVec 64) : Option ImmediateArithmetic.Immediate :=
  let bits8 := BitVec.ofNat 8 value.toNat
  if BitVec.signExtend 64 bits8 = value then some (.i8 bits8)
  else
    let bits32 := BitVec.ofNat 32 value.toNat
    if BitVec.signExtend 64 bits32 = value then some (.i32 bits32) else none

theorem selectSignedImmediate?_recovers {value : BitVec 64}
    {immediate : ImmediateArithmetic.Immediate}
    (success : selectSignedImmediate? value = some immediate) :
    match immediate with
    | .i8 bits => BitVec.signExtend 64 bits = value
    | .i32 bits => BitVec.signExtend 64 bits = value := by
  unfold selectSignedImmediate? at success
  simp only at success
  split at success
  · cases success
    assumption
  · split at success
    · cases success
      assumption
    · contradiction

theorem selectSignedImmediate?_prefers_i8 {value : BitVec 64}
    (fits : BitVec.signExtend 64 (BitVec.ofNat 8 value.toNat) = value) :
  selectSignedImmediate? value =
      some (.i8 (BitVec.ofNat 8 value.toNat)) := by
  unfold selectSignedImmediate?
  dsimp only
  rw [if_pos fits]

def Constant.instruction (constant : Constant) (destination : Gpr) : X86Source.Instruction :=
  match constant with
  | .stdOutputHandle =>
      ⟨.mov, [.register ⟨destination, .w32⟩, .symbol "STD_OUTPUT_HANDLE"]⟩
  | .invalidHandleValue =>
      ⟨.cmp, [.register ⟨destination, .w64⟩, .symbol "INVALID_HANDLE_VALUE"]⟩

def Constant.encode? (constant : Constant) (destination : Gpr) : Option InsnEncoding :=
  match constant with
  | .stdOutputHandle =>
      X86ClosedEncoding.encode
        ⟨.mov, [.register ⟨destination, .w32⟩,
          .immediate StdHandleId.output.value.toNat]⟩
  | .invalidHandleValue =>
      (selectSignedImmediate? constant.value).map
        (ImmediateArithmetic.encode .cmp .w64 destination)

structure Result where
  private mk ::
  frame : SourceFrame.Result
  item : CodeItem
  constant : Constant
  destination : Gpr
  encoding : InsnEncoding
  member : item ∈ frame.program.collected.code
  instructionExact : item.instruction = constant.instruction destination
  encodingExact : constant.encode? destination = some encoding

def resolve? (frame : SourceFrame.Result) (item : CodeItem) : Option Result :=
  if member : item ∈ frame.program.collected.code then
    match instruction : item.instruction with
    | ⟨.mov, [.register ⟨destination, .w32⟩, .symbol "STD_OUTPUT_HANDLE"]⟩ =>
      let constant := Constant.stdOutputHandle
      match encoded : constant.encode? destination with
      | some encoding => some ⟨frame, item, constant, destination, encoding, member,
          instruction, encoded⟩
      | none => none
    | ⟨.cmp, [.register ⟨destination, .w64⟩, .symbol "INVALID_HANDLE_VALUE"]⟩ =>
      let constant := Constant.invalidHandleValue
      match encoded : constant.encode? destination with
      | some encoding => some ⟨frame, item, constant, destination, encoding, member,
          instruction, encoded⟩
      | none => none
    | _ => none
  else none

theorem resolve?_source {frame : SourceFrame.Result} {item : CodeItem} {result : Result}
    (success : resolve? frame item = some result) :
    result.frame = frame ∧ result.item = item ∧
      result.item.instruction = result.constant.instruction result.destination := by
  unfold resolve? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  all_goals simp only at success
  all_goals split at success <;> try contradiction
  all_goals cases success; exact ⟨rfl, rfl, Result.instructionExact _⟩

theorem Result.named_value (result : Result) :
    result.constant.value =
      match result.constant with
      | .stdOutputHandle => BitVec.setWidth 64 StdHandleId.output.value
      | .invalidHandleValue => GetStdHandleResult.invalidHandleValue := by
  cases result.constant <;> rfl

theorem Result.encoding_decodes (result : Result) (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (result.encoding.toBytes ++ rest) = .ok (result.encoding, rest) := by
  cases hc : result.constant with
  | stdOutputHandle =>
      have he : X86ClosedEncoding.encode
          ⟨.mov, [.register ⟨result.destination, .w32⟩,
            .immediate StdHandleId.output.value.toNat]⟩ =
          some result.encoding := by
        simpa [Constant.encode?, hc] using result.encodingExact
      exact X86ClosedEncoding.encode_decodes he rest
  | invalidHandleValue =>
      have he : (selectSignedImmediate? Constant.invalidHandleValue.value).map
          (ImmediateArithmetic.encode .cmp .w64 result.destination) = some result.encoding := by
        simpa [Constant.encode?, hc] using result.encodingExact
      obtain ⟨immediate, selected, encoded⟩ := Option.map_eq_some_iff.mp he
      rw [← encoded]
      exact ImmediateArithmetic.decode_encode .cmp .w64 result.destination immediate rest

end Grass.Assembly.Win32Constants
