import Grass.Unsafe.Step
import Tests.Op.FakeIsa

namespace Grass.Tests.Unsafe.Step

open Grass Grass.ISA.X86 Grass.Op Grass.Unsafe

private def encoding : InsnEncoding :=
  { rex := none
    escape := false
    opcode := 0x8D
    modrm := none
    sib := some default
    disp := .none
    imm := .none }

private def instruction : Construct.X86Instruction :=
  Construct.x86Instruction encoding .encodingShape
    [.applicability, .controlTargets]

private def stepped : Unsafe.Step.Result :=
  Unsafe.Step.step Grass.Tests.FakeIsa.policy Grass.Tests.FakeIsa.state₀ instruction
    (SomeOperation.of Grass.Tests.FakeIsa.Alpha.load)
    Grass.Tests.FakeIsa.thread₀ .thread ⟨⟨"alpha"⟩⟩

example : stepped.instruction.value = encoding := rfl
example : stepped.instruction.taint =
    ⟨.semantics, [.encodingShape, .applicability, .controlTargets]⟩ := rfl
example : stepped.outcome = Grass.Tests.FakeIsa.stepAlpha
    Grass.Tests.FakeIsa.state₀ .load := rfl
example : ∃ state, stepped.outcome.state? = some state := by
  change ∃ state, (Grass.Tests.FakeIsa.stepAlpha Grass.Tests.FakeIsa.state₀
    .load).state? = some state
  rcases Grass.Tests.FakeIsa.load_runs with ⟨state, ran, _, _⟩
  exact ⟨state, ran⟩

example : MissingCheck.controlTargets ∈ stepped.instruction.taint.additional := by
  exact Unsafe.Step.step_retains_additional _ _ _ _ _ _ _ _ (by simp [instruction])

example : MissingCheck.encodingShape ∈ stepped.instruction.taint.additional := by
  exact Unsafe.Step.step_retains_primary _ _ _ _ _ _ _ _

end Grass.Tests.Unsafe.Step
