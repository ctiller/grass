import Grass.Assembly.FrameMemorySource
import Grass.Platform.Win32.CpuPolicy
import Grass.Platform.Win32.WriteFileArguments
import Grass.ISA.X86.Execution.MemoryMoveFactory

/-! Canonical count-slot identity comes from the source frame and fixed loaded
stack policy. No instruction that computes R9 is required by this contract. -/

namespace Grass.Refinement.Console.WriteFileCountArgument

open Grass.Assembly Grass.Memory Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile

/-- The selected DWORD local and fixed stack provenance determine the argument.
The incoming-state checker separately checks actual R9 and memory authority. -/
def argument (policy : CpuAccessPolicy) {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (selectedLocal : SourceResolve.LoadSelection source) : Argument :=
  ⟨policy.stack, selectedLocal.result.address.range⟩

theorem argument_width (policy : CpuAccessPolicy) {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (selectedLocal : SourceResolve.LoadSelection source) :
    (argument policy selectedLocal).range.size = 4 := selectedLocal.result.load_width

theorem argument_stack_selected {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {policy : CpuAccessPolicy} {before : State}
    (selected : Cpu.policy? loaded before = some policy)
    {frame : SourceFrame.Result} {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset}
    (selectedLocal : SourceResolve.LoadSelection source) :
    loaded.stackProvenance? = some (argument policy selectedLocal).provenance := by
  obtain ⟨_, _, _, stack, _, exactStack, _⟩ := Cpu.policy?_inputs selected
  exact stack.trans (congrArg some exactStack.symm)

theorem stack_same {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {left right : CpuAccessPolicy}
    {before after : State} (leftSelected : Cpu.policy? loaded before = some left)
    (rightSelected : Cpu.policy? loaded after = some right) : right.stack = left.stack := by
  obtain ⟨_, _, _, leftStack, _, leftExact, _⟩ := Cpu.policy?_inputs leftSelected
  obtain ⟨_, _, _, rightStack, _, rightExact, _⟩ := Cpu.policy?_inputs rightSelected
  exact rightExact.trans ((Option.some.inj (rightStack.symm.trans leftStack)).trans leftExact.symm)

/-- Static selections for the same local in the same frame resolve identically. -/
theorem range_same {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (left right : SourceResolve.LoadSelection source)
    (sameSlot : left.result.slot = right.result.slot) :
    left.result.address.range = right.result.address.range := by
  have leftSource := FrameLoad.resolve?_source left.success
  have rightSource := FrameLoad.resolve?_source right.success
  have leftAddress := left.result.addressExact
  have rightAddress := right.result.addressExact
  rw [leftSource.1, leftSource.2.2, sameSlot] at leftAddress
  rw [rightSource.1, rightSource.2.2] at rightAddress
  exact congrArg LocalAddress.Result.range (Option.some.inj (leftAddress.symm.trans rightAddress))

end Grass.Refinement.Console.WriteFileCountArgument
