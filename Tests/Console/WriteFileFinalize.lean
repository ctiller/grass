import Grass.Refinement.Console.WriteFileFinalize

namespace Grass.Tests.Console.WriteFileFinalize

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.Loader Grass.Platform.Win32.ExecutionState
open Grass.Refinement.Console.WriteFileResume

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
  {displacement : BitVec 32}
  {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
  {before : RawState} {settled : ProtocolState} {callId : CallProtocol.CallId}
  {runtime : CallRuntime} {frame : ReturnFrame}

/-- Consuming runtime prevents reusing the same original link for another resume. -/
example
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call)
    (caller : ContextId) :
    ¬ ProviderResume.Link
      { resume.after.eraseCall callId with control := .caller caller } callId runtime frame call := by
  intro replay
  have removed := (finalized_fields resume caller).2.2.2.1
  have found := replay.runtimeLookup
  rw [removed] at found
  contradiction

/-- A second live runtime is retained exactly; finalization does not empty the table. -/
example
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call)
    (caller : ContextId) {other : CallProtocol.CallId} (different : other ≠ callId)
    {otherRuntime : CallRuntime} (present : before.calls.lookup other = some otherRuntime) :
    ({ resume.after.eraseCall callId with control := .caller caller } : RawState).calls.lookup other = some otherRuntime := by
  rw [(finalized_fields resume caller).2.2.2.2 other different, resume.raw_frame.2.2]
  exact present

/-- The successful slot read contributes a real event; its machine cannot be
replaced with the settled pre-read machine even though memory is preserved. -/
example
    (resume : ProviderResume.Success loaded (afterReturn before settled) callId runtime frame call) :
    resume.after.machine.machine ≠ settled.machine := by
  intro erasedRead
  obtain ⟨event, appended, _⟩ := resume.slot.receipt.event
  have machine := resume.machine_afterRead.symm.trans erasedRead
  have lengths := congrArg (fun state : MachineState => state.events.length) machine
  rw [appended, List.length_append] at lengths
  simp only [afterReturn, List.length_singleton] at lengths
  omega

end Grass.Tests.Console.WriteFileFinalize
