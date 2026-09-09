import Grass.ISA.X86.Execution.BodyComputationFactory
import Grass.Refinement.Console.WriteAllHead

/-! Connect retained checked CPU successes to the continuous source-loop receipt
consumers. These adapters do not assert factory success, source reachability,
provider return, or caller-model adequacy. Source binding remains the existing
`SourceUpdate` obligation on the resulting receipts.
-/

namespace Grass.Refinement.Console.WriteAllFactory

open Grass.ISA.X86 Grass.ISA.X86.Execution
open BodyComputationFactory WriteAllX86

/-- Preserve the actual ADD/SUB/JMP success chain, with no new CPU transition. -/
def update {policy : CpuAccessPolicy} {before : State}
    (add : ArithmeticSuccess policy before)
    (subtract : ArithmeticSuccess policy add.result)
    (jump : BranchSuccess policy subtract.result)
    (addSelected : add.instruction = .add .w64 .r13 .rax)
    (subSelected : subtract.instruction = .sub .w32 .r14 .rax)
    (displacement : BitVec 32)
    (jumpSelected : jump.instruction = .jump displacement) : UpdateRun before := by
  rcases add with ⟨af, ai, flags, ac, ar, ae, ast⟩
  rcases subtract with ⟨sf, si, sflags, sc, sr, se, sst⟩
  rcases jump with ⟨jf, ji, jc, jr, je⟩
  dsimp only at addSelected subSelected jumpSelected
  subst ai si ji
  exact ⟨af.after, ac, ar, sf.after, sc, sr, jf.after, jc, displacement, jr⟩

theorem update_result {policy : CpuAccessPolicy} {before : State}
    (add : ArithmeticSuccess policy before)
    (subtract : ArithmeticSuccess policy add.result)
    (jump : BranchSuccess policy subtract.result)
    (addSelected : add.instruction = .add .w64 .r13 .rax)
    (subSelected : subtract.instruction = .sub .w32 .r14 .rax)
    (displacement : BitVec 32)
    (jumpSelected : jump.instruction = .jump displacement) :
    (update add subtract jump addSelected subSelected displacement jumpSelected).result =
      jump.result := by
  rcases add with ⟨af, ai, flags, ac, ar, ae, ast⟩
  rcases subtract with ⟨sf, si, sflags, sc, sr, se, sst⟩
  rcases jump with ⟨jf, ji, jc, jr, je⟩
  dsimp only at addSelected subSelected jumpSelected
  subst ai si ji
  rfl

/-- The source consumer sees the same three fetched occurrences retained by the
checked factories, not replacement receipts with matching instruction bytes. -/
theorem update_fetches {policy : CpuAccessPolicy} {before : State}
    (add : ArithmeticSuccess policy before)
    (subtract : ArithmeticSuccess policy add.result)
    (jump : BranchSuccess policy subtract.result)
    (addSelected : add.instruction = .add .w64 .r13 .rax)
    (subSelected : subtract.instruction = .sub .w32 .r14 .rax)
    (displacement : BitVec 32)
    (jumpSelected : jump.instruction = .jump displacement) :
    let run := update add subtract jump addSelected subSelected displacement jumpSelected
    HEq run.add.execution.fetch add.fetched.dispatched.fetch ∧
    HEq run.subtract.execution.fetch subtract.fetched.dispatched.fetch ∧
    HEq run.jump.execution.fetch jump.fetched.dispatched.fetch := by
  rcases add with ⟨af, ai, flags, ac, ar, ae, ast⟩
  rcases subtract with ⟨sf, si, sflags, sc, sr, se, sst⟩
  rcases jump with ⟨jf, ji, jc, jr, je⟩
  dsimp only at addSelected subSelected jumpSelected
  subst ai si ji
  exact ⟨heq_of_eq ae, heq_of_eq se, heq_of_eq je⟩

/-- The checked suffix ends at the authored head with its advanced cursor and
saved handle. Physical return and the full-RAX load remain explicit inputs. -/
theorem update_reenters_head {policy : CpuAccessPolicy} {before : State}
    (add : ArithmeticSuccess policy before)
    (subtract : ArithmeticSuccess policy add.result)
    (jump : BranchSuccess policy subtract.result)
    (addSelected : add.instruction = .add .w64 .r13 .rax)
    (subSelected : subtract.instruction = .sub .w32 .r14 .rax)
    (displacement : BitVec 32)
    (jumpSelected : jump.instruction = .jump displacement)
    {frame : Grass.Assembly.SourceFrame.Result} {rootOffset : Nat}
    {source : Grass.Assembly.SourceResolve.Result frame rootOffset}
    {selected : Grass.Assembly.WriteAllLoopSource.Selection source}
    {bound : SourceUpdate source
      (update add subtract jump addSelected subSelected displacement jumpSelected)}
    (authored : AuthoredUpdate selected bound)
    {payload : Grass.Std.Logical.Vec Grass.Std.Logical.Byte} {base : Nat}
    {cursor : Grass.Std.Console.WriteCursor payload}
    (placed : CursorRegisters payload base cursor before)
    (count : Grass.Std.Console.WriteCount cursor)
    (loaded : (before.gpr .rax).toNat = count.value) :
    CursorRegisters payload base (Grass.Std.Console.advance cursor count) jump.result ∧
    jump.result.gpr .r12 = before.gpr .r12 ∧
    jump.result.rip = BitVec.ofNat 64 (bound.addSite.loadedImageBase +
      Grass.Assembly.SourceResolve.sourceOffset source.codeBase source.splice.finalSizes
        selected.candidate.headIndex) := by
  have closed := authored.reenters_head placed count loaded
  rw [update_result] at closed
  exact closed

end Grass.Refinement.Console.WriteAllFactory
