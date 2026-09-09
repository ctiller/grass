import Grass.Refinement.Console.WriteAllX86
import Grass.Assembly.WriteAllLoopSource

/-! Bind the actual update suffix to the checked authored write_head occurrence.
The execution and successful initialized load remain inputs to this composition.
-/

namespace Grass.Refinement.Console.WriteAllX86

open Grass.Assembly Grass.ISA.X86.Execution Grass.Std.Console Grass.Std.Logical

structure AuthoredUpdate {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset}
    (selected : WriteAllLoopSource.Selection source) {before : State} {run : UpdateRun before}
    (bound : SourceUpdate source run) : Prop where
  addSelected : bound.addSite.output = selected.candidate.add.output
  subSelected : bound.subSite.output = selected.candidate.subtract.output
  jumpSelected : bound.jumpSite.output = selected.candidate.jump.output

theorem AuthoredUpdate.target_is_head {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {selected : WriteAllLoopSource.Selection source}
    {before : State} {run : UpdateRun before} {bound : SourceUpdate source run}
    (authored : AuthoredUpdate selected bound) :
    bound.targetIndex = selected.candidate.headIndex := by
  have target := selected.valid.2.2.2.2.2.2.2.1
  rw [← authored.jumpSelected] at target
  unfold WriteAllLoopSource.branchTarget at target
  rw [bound.branchDetail] at target
  exact Option.some.inj target

/-- The actual final RIP is the source-derived annotated head, not merely an
arbitrary source branch target with the same numeric cursor. -/
theorem AuthoredUpdate.rip_head {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {selected : WriteAllLoopSource.Selection source}
    {before : State} {run : UpdateRun before} {bound : SourceUpdate source run}
    (authored : AuthoredUpdate selected bound) :
    run.result.rip = BitVec.ofNat 64 (bound.addSite.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes selected.candidate.headIndex) := by
  rw [bound.rip_source_target, authored.target_is_head]

/-- At the exact authored back edge, reestablish the numeric cursor and saved
handle at the actual head RIP. The load premise is full-RAX numeric equality;
the outer return/load execution chain must justify it. -/
theorem AuthoredUpdate.reenters_head {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {selected : WriteAllLoopSource.Selection source}
    {before : State} {run : UpdateRun before} {bound : SourceUpdate source run}
    (authored : AuthoredUpdate selected bound) {payload : Vec Byte} {base : Nat}
    {cursor : WriteCursor payload} (placed : CursorRegisters payload base cursor before)
    (count : WriteCount cursor) (loaded : (before.gpr .rax).toNat = count.value) :
    CursorRegisters payload base (advance cursor count) run.result ∧
    run.result.gpr .r12 = before.gpr .r12 ∧
    run.result.rip = BitVec.ofNat 64 (bound.addSite.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes selected.candidate.headIndex) :=
  ⟨run.cursor_advanced placed count loaded, run.gpr_frame .r12 (by decide) (by decide), authored.rip_head⟩

end Grass.Refinement.Console.WriteAllX86
