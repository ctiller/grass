import Grass.Platform.Win32.WriteFilePrepare
import Grass.Platform.Win32.WriteFileStackPlan
import Grass.Platform.Win32.WriteFileCall

/-! Compute the existing call handoff from checked incoming arguments and
the shared stack-plan producer. No argument-producing instruction is required. -/

namespace Grass.Refinement.Console.WriteFileSourceEntry

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState

/-- Compose existing checked doors on the actual CALL result, retaining the
original protocol metadata. No new carrier or return semantics are introduced. -/
def prepareCall? {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} (before : ExecutionState.State ApiRequest)
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    (call : CallNormal before.machine afterFetch afterTarget afterCall displacement)
    (binding : CallPolicy loaded call) (ready : before.ControlConsistent)
    (buffer count : Argument) (bytes : Vec Byte) (fifth : Argument) (provider : ContextId) :
    Option (CallHandoff loaded before call (EntryFactory.requestOf call.result buffer count bytes) provider) := by
  cases reachedEq : reachedCall? before call with
  | none => exact none
  | some reached =>
      have same := (reachedCall?_fields reachedEq).1
      rcases reached with ⟨machine, metadata, control, valid⟩
      dsimp only at same
      subst machine
      cases preparedEq : EntryFactory.prepare? call.result buffer count bytes fifth with
      | error _ => exact none
      | ok entry =>
          cases plannedEq : Abi.StackPlanFactory.deriveLoaded? binding entry with
          | error _ => exact none
          | ok plan =>
              cases handedEq : entryHandoff? ⟨call.result, metadata, control, valid⟩
                  (EntryFactory.requestOf call.result buffer count bytes) plan provider with
              | none => exact none
              | some handoff =>
                  exact if caller : handoff.caller = inputs.thread then
                    some { policy := binding, callerReady := ready
                           reached := ⟨call.result, metadata, control, valid⟩
                           reachedExact := reachedEq, abi := plan
                           continuation := Abi.StackPlanFactory.loaded_continuation_exact plannedEq
                           returnProvenance := Abi.StackPlanFactory.loaded_return_provenance_exact plannedEq
                           returnRange := Abi.StackPlanFactory.loaded_return_range_exact plannedEq
                           handoff := handoff, caller := caller }
                  else none

end Grass.Refinement.Console.WriteFileSourceEntry
