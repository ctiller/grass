import Grass.Unsafe.Step
import Tests.Op.FakeIsa

/-!
# Executable stepping adapter fixtures

The fixture runs one operation, records one rejection, and retains the exact
unattempted suffix while using the generic operation transition unchanged.
-/

namespace Grass.Tests.Unsafe.Step

open Grass Grass.CFG Grass.Memory Grass.Op Grass.Tests.FakeIsa Grass.Unsafe

private def block : BlockId := ⟨⟨"test.unsafe.step", "entry"⟩⟩

private def contract : BlockContract Nat where
  requires := fun _ => True
  exits := []

private def graph : CFG.Graph Nat String where
  entry := block
  blocks := [⟨block, contract, []⟩]

private def targetPolicy : TargetPolicy Nat String where
  graph := graph
  graphWellFormed := by decide
  indirect := []
  indirectSitesUnique := by decide

private def loaded : SomeOperation := SomeOperation.of Alpha.load
private def rejected : SomeOperation := SomeOperation.of Beta.undeclared
private def unattempted : SomeOperation := SomeOperation.of Alpha.store

private def program : ImportedProgram Nat String Nat SomeOperation where
  sourceBytes := [0, 1, 2]
  instructions := [
    ⟨0, [0], loaded, []⟩,
    ⟨1, [1], rejected, []⟩,
    ⟨2, [2], unattempted, []⟩]
  bytesExact := rfl
  ready := by decide
  policy := targetPolicy
  targetsResolved := by simp [ImportTargetsResolved]
  taint := ⟨.importedBytes, "step fixture"⟩

private def adapter : StepAdapter SomeOperation where
  operation := id
  context _ := thread₀
  contextKind _ := .thread
  cause _ := ⟨⟨"unsafe.step"⟩⟩

private def trace : StepTrace Nat SomeOperation program.instructions :=
  stepProgram adapter Grass.Tests.FakeIsa.policy state₀ program

example : trace.attemptedOffsets = [0, 1] := by decide
example : trace.rejections = [.facetsNotClosed .memoryEffects] := by decide
example : trace.remainingOffsets = [2] := by decide
example : trace.records.length = 2 := by decide
example : trace.records.map StepRecord.imported ++ trace.remaining =
    program.instructions := trace.coverage

example (imported : ImportedInstruction Nat SomeOperation) (state : MachineState) :
    stepImported adapter Grass.Tests.FakeIsa.policy state imported =
      Grass.Op.step Grass.Tests.FakeIsa.policy state imported.instruction
        thread₀ .thread ⟨⟨"unsafe.step"⟩⟩ := rfl

end Grass.Tests.Unsafe.Step
