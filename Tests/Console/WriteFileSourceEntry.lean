import Grass.Refinement.Console.WriteFileSourceEntry
import Tests.Platform.Win32WriteFilePrepare

namespace Grass.Tests.Console.WriteFileSourceEntry

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Refinement.Console.WriteFileSourceEntry
open Grass.Tests.Win32WriteFileStackPlan

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def protocol : CallProtocol.State ApiRequest :=
  CallProtocol.initial initial.machine FreshSupply.initial (by decide)

def before : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol protocol initial rfl (.caller inputs.thread)

theorem ready : before.ControlConsistent := by
  refine ⟨protocol, ExecutionState.State.ofCallProtocol_callProtocol? _ _ _ _, ⟨.thread, ?_⟩, ?_⟩
  · decide
  · decide

/-- This fixture starts before the actual CALL, so the composed producer must
repack its retained metadata rather than invent a fresh post-CALL protocol. -/
def prepared := prepareCall? before called.receipt binding ready
  request.buffer request.countSlot request.bytes fifthArgument inputs.independentContext

theorem actual_call_handoff : prepared.isSome := by decide

def handoff := prepared.get (by decide)

theorem count_retained : handoff.handoff.record.request.countSlot = request.countSlot := rfl

theorem original_metadata_retained : handoff.reached.metadata = before.metadata :=
  (WriteFile.reachedCall?_fields handoff.reachedExact).2.1

/-- A wrong canonical count argument cannot pass by retaining the numeric R9
value: preparation checks that numeric address against the supplied argument. -/
theorem wrong_count_refuses :
    (prepareCall? before called.receipt binding ready request.buffer
      { request.countSlot with range := ⟨20, 4⟩ } request.bytes fifthArgument
      inputs.independentContext).isNone := by decide

end Grass.Tests.Console.WriteFileSourceEntry
