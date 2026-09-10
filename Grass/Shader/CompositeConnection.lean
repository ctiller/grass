import Grass.ISA.SPIRV.Composite
import Grass.Shader.WGSL.Composite

/-!
The common value boundary exercised by the two bounded shader targets.

This is a local connection under an explicit correspondence between operands.
It is not a compiler from arbitrary WGSL to SPIR-V, nor a complete shader
execution theorem. The SPIR-V words are decoded and the WGSL tokens parsed;
explicit checked-selection premises supply the four semantic values under
the operand correspondence. No relation between GPU providers is assumed.
-/
namespace Grass.Shader.CompositeConnection

open Grass.ISA

/-- Compare the component values without equating target syntax or host state. -/
def components {α : Type} (value : WGSL.Composite.Vec4 α) : List α :=
  [value.x, value.y, value.z, value.w]

/-- Equal input components give equal constructor results in both target models.
The token and word readers stay in the statement so substituting a different
artifact is not hidden behind a theorem about an unrelated typed expression. -/
theorem checked_construct4_agrees {α : Type}
    (context : SPIRV.Composite.Context) (words : List SPIRV.Composite.Word)
    (decoded : SPIRV.Composite.Result context)
    (instruction : SPIRV.Composite.Construct4)
    (hwords : SPIRV.Composite.decode context words = .ok decoded)
    (hinstruction : decoded.checked.val = .construct4 instruction)
    (environment : WGSL.Composite.Identifier → Option (WGSL.Composite.Operand α))
    (tokens : List WGSL.Composite.Token) (source : WGSL.Composite.Source)
    (htokens : WGSL.Composite.parse? tokens = some source)
    (before : SPIRV.Composite.Store α) (x y z w : α)
    (hx : WGSL.Composite.select? environment source.first = some x)
    (hy : WGSL.Composite.select? environment source.second = some y)
    (hz : WGSL.Composite.select? environment source.third = some z)
    (hw : WGSL.Composite.select? environment source.fourth = some w)
    (sx : before instruction.x = some (.scalar x))
    (sy : before instruction.y = some (.scalar y))
    (sz : before instruction.z = some (.scalar z))
    (sw : before instruction.w = some (.scalar w)) :
    words = (SPIRV.Composite.Instruction.construct4 instruction).encode ++ decoded.rest ∧
    WGSL.Composite.check? environment tokens = some ⟨x, y, z, w⟩ ∧
    ∃ after, decoded.effect before = some after ∧
      after instruction.result = some (.vector (components (WGSL.Composite.Vec4.mk x y z w))) := by
  constructor
  · simpa only [hinstruction] using SPIRV.Composite.decode_ok_framing hwords
  constructor
  · simp [WGSL.Composite.check?, htokens, WGSL.Composite.decode?, hx, hy, hz, hw]
  · refine ⟨(fun id => if id = instruction.result then
        some (.vector [x, y, z, w]) else before id), ?_, ?_⟩
    · simp [SPIRV.Composite.Result.effect, hinstruction, SPIRV.Composite.transfer, sx, sy, sz, sw]
    · simp [components]

end Grass.Shader.CompositeConnection
