import Grass.Assembly.FrameMemorySource
import Grass.Platform.Win32.CpuPolicy
import Grass.Platform.Win32.WriteFileArguments
import Grass.ISA.X86.Execution.MemoryMoveFactory
import Grass.ISA.X86.Execution.CallNormal

/-! Canonical count-slot identity uses the actual CALL's pre-call frame origin,
the source-local displacement, and fixed loaded stack provenance. Source layout
coordinates are not runtime allocation offsets. No R9-producing LEA is required. -/

namespace Grass.Refinement.Console.WriteFileCountArgument

open Grass.Assembly Grass.Memory Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile

/-- The end of the actual CALL's checked saved slot is its pre-call frame
origin. The existing incoming-state checker verifies the resulting current
range, nonwrapping address, R9, and memory authority. -/
def argument (policy : CpuAccessPolicy) {before : State}
    {afterFetch afterRead afterStore : Grass.Memory.MachineState} {displacement : BitVec 32}
    (call : CallNormal before afterFetch afterRead afterStore displacement)
    {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (selectedLocal : SourceResolve.LoadSelection source) : Argument :=
  ⟨policy.stack, ⟨call.storeDescriptor.range.stop + selectedLocal.result.address.displacement,
    selectedLocal.result.address.width⟩⟩

theorem argument_width (policy : CpuAccessPolicy) {before : State}
    {afterFetch afterRead afterStore : Grass.Memory.MachineState} {displacement : BitVec 32}
    (call : CallNormal before afterFetch afterRead afterStore displacement)
    {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (selectedLocal : SourceResolve.LoadSelection source) :
    (argument policy call selectedLocal).range.size = 4 := selectedLocal.result.load_width

/-- Natural-number coordinates recover the actual pre-call RSP before adding
the source displacement. No modular subtraction supplies an unchecked origin. -/
theorem argument_origin (policy : CpuAccessPolicy) {before : State}
    {afterFetch afterRead afterStore : Grass.Memory.MachineState} {displacement : BitVec 32}
    (call : CallNormal before afterFetch afterRead afterStore displacement)
    {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (selectedLocal : SourceResolve.LoadSelection source)
    (base : MachineAddress) (placed : call.storeRun.resolved.allocation.base = some base) :
    base.toNat + (argument policy call selectedLocal).range.start =
      (before.gpr .rsp).toNat + selectedLocal.result.address.displacement := by
  have origin := call.store_stop_toNat base placed
  change base.toNat + (call.storeDescriptor.range.stop + selectedLocal.result.address.displacement) = _
  omega

theorem argument_stack_selected {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {policy : CpuAccessPolicy} {before : State}
    (selected : Cpu.policy? loaded before = some policy)
    {afterFetch afterRead afterStore : Grass.Memory.MachineState} {displacement : BitVec 32}
    (call : CallNormal before afterFetch afterRead afterStore displacement)
    {frame : SourceFrame.Result} {rootOffset : Nat} {source : SourceResolve.Result frame rootOffset}
    (selectedLocal : SourceResolve.LoadSelection source) :
    loaded.stackProvenance? = some (argument policy call selectedLocal).provenance := by
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
theorem address_same {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} (left right : SourceResolve.LoadSelection source)
    (sameSlot : left.result.slot = right.result.slot) :
    left.result.address = right.result.address := by
  have leftSource := FrameLoad.resolve?_source left.success
  have rightSource := FrameLoad.resolve?_source right.success
  have leftAddress := left.result.addressExact
  have rightAddress := right.result.addressExact
  rw [leftSource.1, leftSource.2.2, sameSlot] at leftAddress
  rw [rightSource.1, rightSource.2.2] at rightAddress
  exact Option.some.inj (leftAddress.symm.trans rightAddress)

end Grass.Refinement.Console.WriteFileCountArgument
