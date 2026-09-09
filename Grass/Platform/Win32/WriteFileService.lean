import Grass.Platform.Win32.WriteFile
import Grass.Platform.Win32.RawState

/-!
# Runtime-indexed WriteFile servicing

These receipts connect actual committed provider actions to the per-call runtime
frontier and compute the resulting raw carrier. They remain conditional on the
selected provider realization. They are not exhaustive raw-step classification
or native provider adequacy evidence.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState

/-- A committed service action reads its frontier and fixed ABI plan from the
actual runtime entry. Its output carrier is computed below, never supplied. -/
structure ServiceReceipt (realization : Realization) (before : RawState)
    (call : CallProtocol.CallId) (record : CallProtocol.Pending Request)
    (action : Action) (output : Vec Byte) where
  protocol : ProtocolState
  projected : before.metadata.pack? before.machine.machine = some protocol
  runtime : Grass.Platform.Win32.WriteFileRuntime
  runtimeLookup : before.calls.lookup call = some (.writeFile runtime)
  control : before.control = .pending call record.caller record.agent
  pre : Prefix runtime.loanPlan protocol call record
  accepted : pre.accepted = runtime.accepted
  nextProtocol : ProtocolState
  post : Prefix runtime.loanPlan nextProtocol call record
  committed : CommittedStep realization pre post action output

namespace ServiceReceipt

variable {realization : Realization} {before : RawState} {call : CallProtocol.CallId}
  {record : CallProtocol.Pending Request} {action : Action} {output : Vec Byte}

/-- Only the accepted frontier is updated by a service receipt. -/
def nextRuntime (receipt : ServiceReceipt realization before call record action output) :
    Grass.Platform.Win32.WriteFileRuntime :=
  { receipt.runtime with accepted := receipt.post.accepted }

/-- Retain the architectural registers and control, use the actual committed
machine and full metadata, and update only this call's runtime entry. -/
def after (receipt : ServiceReceipt realization before call record action output) : RawState :=
  (ExecutionState.State.ofCallProtocol receipt.nextProtocol
    { before.machine with machine := receipt.nextProtocol.machine } rfl before.control).raw
      (before.calls.insert call (.writeFile receipt.nextRuntime))

theorem after_projected (receipt : ServiceReceipt realization before call record action output) :
    receipt.after.metadata.pack? receipt.after.machine.machine = some receipt.nextProtocol :=
  CallProtocol.State.metadata_pack? receipt.nextProtocol

theorem after_runtimeLookup
    (receipt : ServiceReceipt realization before call record action output) :
    receipt.after.calls.lookup call = some (.writeFile receipt.nextRuntime) :=
  FiniteMap.lookup_insert_self _ _ _

theorem after_accepted (receipt : ServiceReceipt realization before call record action output) :
    receipt.nextRuntime.accepted = receipt.post.accepted := rfl

theorem after_frame (receipt : ServiceReceipt realization before call record action output) :
    receipt.nextRuntime.toReturnFrame = receipt.runtime.toReturnFrame := rfl

theorem after_fifth (receipt : ServiceReceipt realization before call record action output) :
    receipt.nextRuntime.fifthSlot = receipt.runtime.fifthSlot := rfl

theorem after_loanPlan (receipt : ServiceReceipt realization before call record action output) :
    receipt.nextRuntime.loanPlan = receipt.runtime.loanPlan := rfl

theorem after_otherCall (receipt : ServiceReceipt realization before call record action output)
    {other : CallProtocol.CallId} (different : other ≠ call) :
    receipt.after.calls.lookup other = before.calls.lookup other :=
  FiniteMap.lookup_insert_ne _ different _

theorem after_control (receipt : ServiceReceipt realization before call record action output) :
    receipt.after.control = .pending call record.caller record.agent := receipt.control

theorem same_pending (receipt : ServiceReceipt realization before call record action output) :
    receipt.protocol.pending.lookup call = some (embedPending record) ∧
      receipt.nextProtocol.pending.lookup call = some (embedPending record) :=
  ⟨receipt.pre.pending.lookup, receipt.post.pending.lookup⟩

theorem after_machine (receipt : ServiceReceipt realization before call record action output) :
    receipt.after.machine = { before.machine with machine := receipt.nextProtocol.machine } := rfl

theorem after_metadata (receipt : ServiceReceipt realization before call record action output) :
    receipt.after.metadata = receipt.nextProtocol.metadata := rfl

/-- `metadata_unchanged` derives preservation of the whole protocol metadata
from the actual checked step, including every unrelated pending occurrence. -/
theorem metadata_unchanged
    (receipt : ServiceReceipt realization before call record action output) :
    receipt.after.metadata = before.metadata := by
  obtain ⟨calls, grants, pending, boundaries⟩ :=
    CallProtocol.step?_metadata receipt.committed.ran
  have same : receipt.nextProtocol.metadata = receipt.protocol.metadata := by
    simp only [CallProtocol.State.metadata, calls, grants, pending, boundaries]
  exact same.trans (CallProtocol.Metadata.pack?_fields receipt.projected).2

/-- `frontier_continuity` derives equality of consecutive accepted frontiers
from the shared raw state and exact runtime lookup, preventing prefix splicing. -/
theorem frontier_continuity
    (receipt : ServiceReceipt realization before call record action output)
    {nextAction : Action} {nextOutput : Vec Byte}
    (next : ServiceReceipt realization receipt.after call record nextAction nextOutput) :
    next.pre.accepted = receipt.post.accepted ∧
      next.runtime.loanPlan = receipt.runtime.loanPlan := by
  have runtime := CallRuntime.writeFile.inj
    (Option.some.inj (next.runtimeLookup.symm.trans receipt.after_runtimeLookup))
  exact ⟨next.accepted.trans (congrArg Grass.Platform.Win32.WriteFileRuntime.accepted runtime),
    (congrArg Grass.Platform.Win32.WriteFileRuntime.loanPlan runtime).trans receipt.after_loanPlan⟩

end ServiceReceipt

/-- The computed endpoint of an actual conditional service receipt. This does
not assert that every raw edge is a service action or licenses arbitrary policy. -/
def ServiceEdge (realization : Realization) (before : RawState)
    (call : CallProtocol.CallId) (record : CallProtocol.Pending Request)
    (action : Action) (output : Vec Byte) (after : RawState) : Prop :=
  ∃ receipt : ServiceReceipt realization before call record action output, receipt.after = after

end Grass.Platform.Win32.WriteFile
