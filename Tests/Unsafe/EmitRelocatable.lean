import Grass.Unsafe.EmitRelocatable

/-!
# Checked relocatable emission fixtures

Fixtures pin exact one-section bytes and source ranges, empty unresolved link
tables, structural validity, and exact alignment/source-map rejections.
-/

namespace Grass.Tests.Unsafe.EmitRelocatable

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Link
  Grass.Construct.Source Grass.Std.Logical Grass.Unsafe

private structure Instruction where
  payload : List UInt8
deriving Repr, DecidableEq

private def blockId : BlockId := ⟨⟨"test.unsafe.emit-relocatable", "entry"⟩⟩
private def fragmentId : LinkFragmentId :=
  ⟨⟨"test.unsafe.emit-relocatable", "fragment"⟩⟩
private def sectionId : SectionId :=
  ⟨⟨"test.unsafe.emit-relocatable", "text"⟩⟩
private def graph : Graph Unit Unit := ⟨blockId, []⟩
private def first : Instruction := ⟨[0x10, 0x11]⟩
private def second : Instruction := ⟨[0x20]⟩
private def empty : Instruction := ⟨[]⟩
private def lowered (index : Nat) (instruction : Instruction) :
    LoweredInstruction Instruction :=
  ⟨blockId, ⟨[], [], index⟩, instruction⟩
private def program (tail : Instruction) : LoweredProgram Unit Unit Instruction :=
  ⟨graph, [lowered 0 first, lowered 1 tail]⟩
private def encoder : RawEncoder Instruction := ⟨Instruction.payload⟩
private def taint : Taint := ⟨.externalGenerator, "unverified bytes"⟩
private def emission : RawProgramEmission Unit Unit Instruction :=
  emitRawProgram (program second) encoder taint
private def config : RelocatableEmissionConfig :=
  ⟨fragmentId, sectionId, 16, .code, ⟨true, false, true⟩⟩

private def checked : CheckedRelocatableEmission emission config :=
  ⟨by decide, by
    change CheckedLinkSourceMap emission sectionId
    exact ⟨by
      change (0 = 0 ∧ 0 < 2 ∧ (2 = 2 ∧ 0 < 1 ∧ True))
      decide⟩⟩

example : (checkRelocatableEmission emission config).isOk = true := rfl
example : checked.contribution.content.initialized.toList =
    emission.bytes.map Byte.ofUInt8 :=
  checked.sectionBytesExact
example : (checked.fragment (RelocKind := Unit)
    (ImportIdentity := Unit)).sections.map
      (fun contribution => contribution.content.initialized.toList) =
    [[0x10, 0x11, 0x20]] := rfl
example : (checked.fragment (RelocKind := Unit)
    (ImportIdentity := Unit)).sourceMap = [
      ⟨sectionId, 0, 2, blockId, ⟨[], [], 0⟩⟩,
      ⟨sectionId, 2, 1, blockId, ⟨[], [], 1⟩⟩] := rfl
example : (checked.fragment (RelocKind := Unit)
    (ImportIdentity := Unit)).definitions = [] := rfl
example : (checked.fragment (RelocKind := Unit)
    (ImportIdentity := Unit)).relocations = [] := rfl
example : (checked.fragment (RelocKind := Unit)
    (ImportIdentity := Unit)).externals = [] := rfl
example : (checked.fragment (RelocKind := Unit)
    (ImportIdentity := Unit)).entryCandidates = [] := rfl
example : (checked.fragment (RelocKind := Unit)
    (ImportIdentity := Unit)).WellFormed := checked.fragmentWellFormed

private def zeroAlignment : RelocatableEmissionConfig :=
  { config with alignment := 0 }
example : checkRelocatableEmission emission zeroAlignment =
    .error (.zeroAlignment fragmentId sectionId) := rfl

private def zeroWidth : RawProgramEmission Unit Unit Instruction :=
  emitRawProgram (program empty) encoder taint
example : checkRelocatableEmission zeroWidth config =
    .error (.sourceMap (.zeroWidth blockId ⟨[], [], 1⟩ 2)) := rfl

end Grass.Tests.Unsafe.EmitRelocatable
