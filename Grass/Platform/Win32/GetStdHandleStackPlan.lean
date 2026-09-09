import Grass.Platform.Win32.GetStdHandleRuntime
import Grass.Platform.Win32.ReturnHomeStackPlan

namespace Grass.Platform.Win32.GetStdHandle.StackPlanFactory

open Grass.ISA.X86 Grass.ISA.X86.Execution

abbrev Failure := ReturnHome.StackPlanFactory.Failure

abbrev derive? {callBefore : State} {afterFetch afterRead afterStore : Grass.Memory.MachineState}
    {displacement : BitVec 32} (policy : CpuAccessPolicy)
    (call : CallNormal callBefore afterFetch afterRead afterStore displacement) :=
  ReturnHome.StackPlanFactory.derive? policy call

theorem continuation_exact {callBefore : State}
    {afterFetch afterRead afterStore : Grass.Memory.MachineState}
    {displacement : BitVec 32} {policy : CpuAccessPolicy}
    {call : CallNormal callBefore afterFetch afterRead afterStore displacement}
    {plan : GetStdHandle.StackPlan call.result}
    (success : derive? policy call = .ok plan) :
    plan.continuation = call.fetch.site.fallthroughRip :=
  ReturnHome.StackPlanFactory.continuation_exact success

abbrev deriveLoaded? {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {callBefore : State}
    {afterFetch afterRead afterStore : Grass.Memory.MachineState} {displacement : BitVec 32}
    {call : CallNormal callBefore afterFetch afterRead afterStore displacement}
    (binding : WriteFile.CallPolicy loaded call) :
    Except Failure (GetStdHandle.StackPlan call.result) :=
  ReturnHome.StackPlanFactory.deriveLoaded? binding

theorem loaded_continuation_exact {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {callBefore : State}
    {afterFetch afterRead afterStore : Grass.Memory.MachineState} {displacement : BitVec 32}
    {call : CallNormal callBefore afterFetch afterRead afterStore displacement}
    {binding : WriteFile.CallPolicy loaded call} {plan : GetStdHandle.StackPlan call.result}
    (success : deriveLoaded? binding = .ok plan) :
    plan.continuation = call.fetch.site.fallthroughRip :=
  continuation_exact success

end Grass.Platform.Win32.GetStdHandle.StackPlanFactory
