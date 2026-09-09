import Grass.Platform.Win32.GetStdHandleStackPlan

namespace Grass.Tests.Win32GetStdHandleStackPlan

open Grass.Platform.Win32 Grass.ISA.X86.Execution

example {callBefore : State} {afterFetch afterRead afterStore : Grass.Memory.MachineState}
    {displacement : BitVec 32} {policy : CpuAccessPolicy}
    {call : CallNormal callBefore afterFetch afterRead afterStore displacement}
    {plan : GetStdHandle.StackPlan call.result}
    (success : GetStdHandle.StackPlanFactory.derive? policy call = .ok plan) :
    plan.continuation = call.fetch.site.fallthroughRip :=
  GetStdHandle.StackPlanFactory.continuation_exact success

end Grass.Tests.Win32GetStdHandleStackPlan
