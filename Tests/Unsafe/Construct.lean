import Grass.Unsafe.Construct

namespace Grass.Tests.Unsafe.Construct

open Grass Grass.ISA.X86 Grass.Std.Logical Grass.Unsafe

private def malformed : InsnEncoding :=
  { rex := none
    escape := false
    opcode := 0x8D
    modrm := none
    sib := some default
    disp := .none
    imm := .none }

example : ¬malformed.WellFormed := by native_decide

private def admitted : Raw .x86Instruction :=
  Unsafe.Construct.x86Instruction malformed .encodingShape
    [.applicability, .semantics, .controlTargets]

example : admitted.value = malformed := rfl
example : admitted.taint.primary = .encodingShape := rfl
example : admitted.taint.additional =
    [.applicability, .semantics, .controlTargets] := rfl
example : (Unsafe.Construct.x86Bytes admitted).value = malformed.toBytes := rfl
example : (Unsafe.Construct.x86Bytes admitted).taint = admitted.taint := rfl

private def renderedTwice : Raw .bytes :=
  (Unsafe.Construct.x86Bytes admitted).map id

example : renderedTwice.value = malformed.toBytes := rfl
example : renderedTwice.taint = ⟨.encodingShape,
    [.applicability, .semantics, .controlTargets]⟩ := rfl
example : (admitted.map (source := .x86Instruction) (target := .bytes)
      InsnEncoding.toBytes).map
    (source := .bytes) (target := .bytes) id =
    admitted.map (source := .x86Instruction) (target := .bytes)
      (id ∘ InsnEncoding.toBytes) :=
  Raw.map_compose (source := .x86Instruction) (target := .bytes)
    (final := .bytes) InsnEncoding.toBytes id admitted

end Grass.Tests.Unsafe.Construct
