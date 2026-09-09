import Grass.Refinement.Console.WriteAllBody

namespace Grass.Tests.Console.WriteAllBody

open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Memory Grass.Std.Logical Grass.Std.Console
open Grass.Platform.Win32.WriteFile Grass.Refinement.Console.WriteAllX86
open Grass.Refinement.Console.WriteAllBody

/-- A full positive report still executes the guarded body and back edge. It
reaches the head with the full remaining register zero, where the existing head
guard can select success; the body does not manufacture a process outcome. -/
example {policy : CpuAccessPolicy} {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    (run : Run policy source before) {payload : Vec Byte} {base : Nat}
    {cursor : WriteCursor payload} (placed : CursorRegisters payload base cursor before)
    (argument : Argument) (value : BitVec 32)
    (observed : DwordAt before.machine.memory argument value)
    (provenance : run.load.source.access.descriptor.provenance = argument.provenance)
    (range : run.load.source.access.descriptor.range = argument.range)
    (full : value.toNat = cursor.remaining.length) (positive : 0 < value.toNat) :
    (run.update.result.gpr .r14).toNat = 0 ∧
    run.update.result.rip = BitVec.ofNat 64 (run.load.source.site.loadedImageBase +
      SourceResolve.sourceOffset source.codeBase source.splice.finalSizes
        run.selected.candidate.loop.candidate.headIndex) := by
  have closed := run.reenters_head placed argument value observed provenance range
    (Nat.le_of_eq full) positive
  refine ⟨?_, closed.2.2.2.2.2.1⟩
  rw [closed.2.2.1.remaining]
  simp only [WriteCursor.remaining, advance, Vec.length_drop] at full ⊢
  omega

/-- Every positive body execution strictly decreases the remaining rank. The
rank follows the observed count and applies to both partial and full reports. -/
example {policy : CpuAccessPolicy} {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    (run : Run policy source before) {payload : Vec Byte} {base : Nat}
    {cursor : WriteCursor payload} (placed : CursorRegisters payload base cursor before)
    (argument : Argument) (value : BitVec 32)
    (observed : DwordAt before.machine.memory argument value)
    (provenance : run.load.source.access.descriptor.provenance = argument.provenance)
    (range : run.load.source.access.descriptor.range = argument.range)
    (bounded : value.toNat ≤ cursor.remaining.length) (positive : 0 < value.toNat) :
    (run.update.result.gpr .r14).toNat < (before.gpr .r14).toNat := by
  have closed := run.reenters_head placed argument value observed provenance range bounded positive
  rw [closed.2.2.1.remaining, placed.remaining]
  simp only [WriteCursor.remaining, advance, Vec.length_drop] at bounded ⊢
  omega

end Grass.Tests.Console.WriteAllBody
