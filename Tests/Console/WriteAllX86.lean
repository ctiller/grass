import Grass.Refinement.Console.WriteAllX86

namespace Grass.Tests.Console.WriteAllX86

open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Memory Grass.Std.Console Grass.Std.Logical
open Grass.Refinement.Console.WriteAllX86

/-- The zero BOOL branch reaches the actual branch target directly; it has no
DWORD-load premise, including no initialization premise for that slot. -/
example {before : State} {testedFetched testedComputed branchFetched branchComputed : MachineState}
    (tested : ArithmeticNormal before testedFetched testedComputed (.test .w32 .rax .rax))
    (displacement : BitVec 32)
    (branch : BranchNormal tested.result branchFetched branchComputed (.equal displacement))
    (zero : (before.gpr .rax).setWidth 32 = 0) :
    branch.result.rip = branch.target := by
  apply branch.taken_rip
  change tested.result.statusFlags.zf = true
  rw [test_eax_zero tested, zero]
  rfl

/-- At the boundary count==remaining, the unsigned excess branch falls through. -/
example {before : State} {cmpFetched cmpComputed branchFetched branchComputed : MachineState}
    (compared : ArithmeticNormal before cmpFetched cmpComputed (.cmp .w32 .rax .r14))
    (displacement : BitVec 32)
    (branch : BranchNormal compared.result branchFetched branchComputed (.above displacement))
    (full : (before.gpr .rax).setWidth 32 = (before.gpr .r14).setWidth 32) :
    branch.result.rip = branch.execution.fetch.site.fallthroughRip := by
  apply branch.not_taken_rip
  apply cmp_count_no_violation compared
  rw [full]
  exact Nat.le_refl _

/-- The update suffix preserves the loaded full count and saved handle, while
clearing the upper half of the 32-bit remaining register. -/
example {before : State} (run : UpdateRun before) :
    run.result.gpr .rax = before.gpr .rax ∧
    run.result.gpr .r12 = before.gpr .r12 ∧
    BitVec.extractLsb' 32 32 (run.result.gpr .r14) = 0 := by
  refine ⟨run.gpr_frame .rax (by decide) (by decide),
    run.gpr_frame .r12 (by decide) (by decide), ?_⟩
  rw [run.remaining_exact]
  rw [BitVec.setWidth_eq_append (by decide : 32 ≤ 64)]
  exact writeBack.w32_clears_high (before.gpr .r14) _

/-- A low-DWORD equality alone cannot justify the following 64-bit pointer ADD.
The actual successful MOV/load must supply its zero-extension connection. -/
example {payload : Vec Byte} {base : Nat} {cursor : WriteCursor payload}
    {before : State} (_run : UpdateRun before)
    (_placed : CursorRegisters payload base cursor before) (_count : WriteCount cursor)
    (_lowOnly : ((before.gpr .rax).setWidth 32).toNat = _count.value) : True := by
  fail_if_success
    have _wrong := _run.cursor_advanced _placed _count _lowOnly
  trivial

/-- A receipt starting from an unrelated state cannot replace the second
instruction of the actual continuous suffix. -/
example {before unrelated : State} (_run : UpdateRun before)
    {fetched computed : MachineState}
    (_other : ArithmeticNormal unrelated fetched computed (.sub .w32 .r14 .rax)) : True := by
  fail_if_success
    have _wrong : ArithmeticNormal _run.add.result fetched computed (.sub .w32 .r14 .rax) := _other
  trivial

end Grass.Tests.Console.WriteAllX86
