import Grass.Unsafe.Import

namespace Grass.Tests.Unsafe.Import

open Grass Grass.CFG Grass.ISA.X86 Grass.Std.Logical Grass.Unsafe.Import

private def block (name : String) : BlockId := ⟨⟨"unsafe-import-test", name⟩⟩
private def targetA := block "a"
private def targetB := block "b"

private def indirect : TargetEvidence :=
  .indirect ⟨.annotation, [targetA, targetB]⟩

example : indirect.WellFormed := by native_decide
example : indirect.declaredTargets = [targetA, targetB] := rfl

private def succeeds (input : ByteSeq) (targets : TargetEvidence) : Bool :=
  match importOne input targets with
  | .ok _ => true
  | .error _ => false

-- `FF /2` with ModR/M `00 010 000` is the modeled indirect near call form.
example : succeeds [0xFF, 0x10, 0x90] indirect = true := by native_decide
example : succeeds [0xFF, 0x10] (.indirect ⟨.analysis, []⟩) = false := by native_decide
example : succeeds [0xFF, 0x10]
    (.indirect ⟨.relocation, [targetA, targetA]⟩) = false := by native_decide
example : succeeds [0x00] .fallthrough = false := by native_decide
example : succeeds [] .fallthrough = false := by native_decide

example {imported : ImportedInstruction}
    (h : importOne [0xFF, 0x10, 0x90] indirect = .ok imported) :
    imported.rest = [0x90] := by
  have decoded := importOne_decode h
  let remainder : Except DecodeError (InsnEncoding × ByteSeq) → ByteSeq
    | .error _ => []
    | .ok (_, rest) => rest
  have restEq := congrArg remainder decoded
  change remainder (decodeInsn [0xFF, 0x10, 0x90]) = imported.rest at restEq
  have computed : remainder (decodeInsn [0xFF, 0x10, 0x90]) = [0x90] := by
    native_decide
  exact restEq.symm.trans computed

example {imported : ImportedInstruction}
    (h : importOne [0xFF, 0x10] indirect = .ok imported) :
    imported.targets = indirect := importOne_targets h

example {imported : ImportedInstruction}
    (h : importOne [0xFF, 0x10] indirect = .ok imported) :
    imported.instruction.taint = importedTaint := importOne_taint h

end Grass.Tests.Unsafe.Import
