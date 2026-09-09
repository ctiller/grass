import Grass.Assembly.FrameMemoryExecution
import Grass.Platform.Win32.WriteFileReturn
import Grass.Op.ReadBytes
import Grass.Refinement.Console.WriteAllX86

/-! Connect the exact initialized WriteFile count slot to an actual source
DWORD load. This does not supply the physical return or its continuation.
-/

namespace Grass.Refinement.Console.WriteFileLoad

open Grass.Assembly Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Platform.Win32.WriteFile

theorem read_value {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (read : ReadValue32 run)
    (argument : Argument) (value : BitVec 32)
    (observed : DwordAt before.memory argument value)
    (provenance : descriptor.provenance = argument.provenance)
    (range : descriptor.range = argument.range) : read.value = value := by
  apply read.value_of_observed_eq_le32
  rw [read.observed_exact]
  congr 1
  rw [read.observed_backing]
  apply observedBytes_eq_of_resolved_bytes run.resolved (le32 value)
    (by rw [read.width]; simp)
  intro i bounded
  have width : (le32 value).length = 4 := by simp
  have small : i < 4 := by omega
  have covered : descriptor.range.Covers (descriptor.range.start + i) := by
    simp only [ByteRange.covers_def]
    rw [read.width]
    omega
  unfold MemoryState.ResolvedAccess.byteAt?
  rw [run.resolved.cellAt?_eq_state covered]
  change (before.memory.cellAt? descriptor.provenance.root (descriptor.range.start + i)).map Prod.fst = _
  rw [provenance, range, observed.2 ⟨i, small⟩]
  have bytes := congrArg Vec.toList (le32_toLittleEndian value)
  have sizeBytes : (Grass.Grammar.bitVecToLittleEndian (count := 4) value).1.toList.length = 4 :=
    (Grass.Grammar.bitVecToLittleEndian (count := 4) value).2
  simp only [Option.map_some]
  congr 1
  exact (congrArg (fun list : List Byte => list[i]?) bytes).symm |> fun equal => by
    exact Option.some.inj (by simpa [List.getElem?_eq_getElem, small, width, sizeBytes] using equal)

/-- The actual load's full destination register is the observed DWORD,
including the architectural zero extension required by the subsequent ADD. -/
theorem load_value {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch afterLoad : MachineState}
    (load : FrameMemoryExecution.LoadNormal source before afterFetch afterLoad)
    (argument : Argument) (value : BitVec 32)
    (observed : DwordAt before.machine.memory argument value)
    (provenance : load.access.descriptor.provenance = argument.provenance)
    (range : load.access.descriptor.range = argument.range) :
    (load.result.gpr load.selection.result.destination).toNat = value.toNat := by
  have afterFetchObserved : DwordAt afterFetch.memory argument value := by
    rw [load.site.fetch.state_frame.1]
    exact observed
  have count := read_value load.read argument value afterFetchObserved provenance range
  change ((before.withGpr load.selection.result.destination
    (writeBack .w32 (before.gpr load.selection.result.destination) load.read.value)).gpr
    load.selection.result.destination).toNat = value.toNat
  rw [State.withGpr_same]
  rw [count]
  change (0#32 ++ value).toNat = value.toNat
  have zeroExtended : (0#32 ++ value) = value.setWidth 64 :=
    (BitVec.setWidth_eq_append (by decide)).symm
  rw [zeroExtended]
  exact BitVec.toNat_setWidth_of_le (by decide)

theorem test_gpr {before : State} {afterFetch afterCompute : MachineState}
    (receipt : ArithmeticNormal before afterFetch afterCompute (.test .w32 .rax .rax)) :
    receipt.result.gpr = before.gpr := by
  funext register
  change (if register = .rax then before.gpr .rax else before.gpr register) = before.gpr register
  split <;> simp_all

theorem cmp_gpr {before : State} {afterFetch afterCompute : MachineState}
    (receipt : ArithmeticNormal before afterFetch afterCompute (.cmp .w32 .rax .r14)) :
    receipt.result.gpr = before.gpr := by
  funext register
  change (if register = .rax then before.gpr .rax else before.gpr register) = before.gpr register
  split <;> simp_all

/-- Continuous post-load TEST/JZ/CMP/JA receipts. Branch outcomes are proved
from the observed count below, not assumed in this carrier. -/
structure CountChecks (before : State) where
  testFetch : MachineState
  testCompute : MachineState
  tested : ArithmeticNormal before testFetch testCompute (.test .w32 .rax .rax)
  zeroFetch : MachineState
  zeroCompute : MachineState
  zeroDisplacement : BitVec 32
  zeroBranch : BranchNormal tested.result zeroFetch zeroCompute (.equal zeroDisplacement)
  cmpFetch : MachineState
  cmpCompute : MachineState
  compared : ArithmeticNormal zeroBranch.result cmpFetch cmpCompute (.cmp .w32 .rax .r14)
  aboveFetch : MachineState
  aboveCompute : MachineState
  aboveDisplacement : BitVec 32
  aboveBranch : BranchNormal compared.result aboveFetch aboveCompute (.above aboveDisplacement)

def CountChecks.result {before : State} (checks : CountChecks before) : State := checks.aboveBranch.result

theorem CountChecks.gpr_frame {before : State} (checks : CountChecks before) :
    checks.result.gpr = before.gpr :=
  checks.aboveBranch.gpr_frame.trans ((cmp_gpr checks.compared).trans
    (checks.zeroBranch.gpr_frame.trans (test_gpr checks.tested)))

theorem CountChecks.memory_frame {before : State} (checks : CountChecks before) :
    checks.result.machine.memory = before.machine.memory :=
  checks.aboveBranch.state_frame.1.trans (checks.compared.state_frame.1.trans
    (checks.zeroBranch.state_frame.1.trans checks.tested.state_frame.1))

theorem CountChecks.positive_fallthrough {before : State} (checks : CountChecks before)
    (positive : 0 < ((before.gpr .rax).setWidth 32).toNat) :
    checks.zeroBranch.result.rip = checks.zeroBranch.execution.fetch.site.fallthroughRip := by
  apply checks.zeroBranch.not_taken_rip
  change checks.tested.result.statusFlags.zf = false
  rw [WriteAllX86.test_eax_zero checks.tested]
  have nonzero : (before.gpr .rax).setWidth 32 ≠ 0 := by
    intro zero
    rw [zero] at positive
    simp at positive
  exact beq_eq_false_iff_ne.mpr nonzero

theorem CountChecks.bounded_fallthrough {before : State} (checks : CountChecks before)
    (bounded : ((before.gpr .rax).setWidth 32).toNat ≤ ((before.gpr .r14).setWidth 32).toNat) :
    checks.aboveBranch.result.rip = checks.aboveBranch.execution.fetch.site.fallthroughRip := by
  apply checks.aboveBranch.not_taken_rip
  apply WriteAllX86.cmp_count_no_violation checks.compared
  rw [checks.zeroBranch.gpr_frame, test_gpr checks.tested]
  exact bounded

/-- Actual load and actual check receipts produce the full count consumed by
the update suffix. Return-slot execution and return-to-load continuity remain
outside this theorem and cannot be replaced by this memory observation. -/
theorem checked_load_value {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch afterLoad : MachineState}
    (load : FrameMemoryExecution.LoadNormal source before afterFetch afterLoad)
    (checks : CountChecks load.result) (argument : Argument) (value : BitVec 32)
    (observed : DwordAt before.machine.memory argument value)
    (provenance : load.access.descriptor.provenance = argument.provenance)
    (range : load.access.descriptor.range = argument.range)
    (destination : load.selection.result.destination = .rax) :
    (checks.result.gpr .rax).toNat = value.toNat := by
  rw [checks.gpr_frame, ← destination]
  exact load_value load argument value observed provenance range

end Grass.Refinement.Console.WriteFileLoad
