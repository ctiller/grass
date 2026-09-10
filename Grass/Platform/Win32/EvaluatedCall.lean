import Grass.Platform.Win32.CpuPolicy
import Grass.Platform.Win32.ExecutionState
import Grass.Platform.Win32.ApiRequest
import Grass.ISA.X86.Execution.CheckedStep

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- The handoff's exact CALL receipt was returned by the fixed checked
evaluator under the selected Windows policy. Standalone success data is not
evaluation provenance. Heterogeneous equality retains the indexed intermediate
states rather than replacing the handoff receipt with a similar CALL. -/
structure EvaluatedCall {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (before : State ApiRequest)
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Grass.ISA.X86.Execution.CallNormal before.machine
      afterFetch afterRead afterStore displacement) where
  policy : Grass.ISA.X86.Execution.CpuAccessPolicy
  selected : Cpu.policy? loaded before.machine = some policy
  flags : Grass.ISA.X86.RegisterSemantics.Flags Bool
  success : Grass.ISA.X86.Execution.CallFactory.Success policy before.machine
  evaluated : Grass.ISA.X86.Execution.CheckedExecution.normal policy before.machine flags =
    some (.ok (.call success))
  receiptExact : HEq success.receipt receipt

end Grass.Platform.Win32.Raw
