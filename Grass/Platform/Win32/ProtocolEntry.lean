import Grass.Platform.Win32.ApiRequest
import Grass.Platform.Win32.ExecutionState

/-!
# Checked protocol entry

This receipt records one successful call-protocol handoff from a checked
Windows execution carrier.  It is independent of an API's semantic request
preparation and of any runtime table update.
-/

namespace Grass.Platform.Win32.ProtocolEntry

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.ExecutionState

/-- A checked handoff of an exact heterogeneous API request and loan batch. -/
structure Entry (before : ExecutionState.State ApiRequest) (request : ApiRequest)
    (loans : List CallProtocol.LoanRequest) (agent : ContextId) where
  caller : ContextId
  control : before.control = .caller caller
  callerRegistered : before.machine.machine.contexts.lookup caller = some .thread
  agentRegistered : before.machine.machine.contexts.lookup agent = some .externalAgent
  clean : before.machine.machine.violations.IsEmpty
  beforeProtocol : CallProtocol.State ApiRequest
  projected : before.callProtocol? = some beforeProtocol
  call : CallProtocol.CallId
  afterProtocol : CallProtocol.State ApiRequest
  issued : CallProtocol.handoff? beforeProtocol caller agent request loans = some (call, afterProtocol)

/-- Issue the fixed request after checking the caller registration and cleanliness. -/
def issue? (before : ExecutionState.State ApiRequest) (request : ApiRequest)
    (loans : List CallProtocol.LoanRequest) (agent : ContextId) :
    Option (Entry before request loans agent) :=
  match control : before.control with
  | .caller caller =>
      if callerRegistered : before.machine.machine.contexts.lookup caller = some .thread then
      if agentRegistered : before.machine.machine.contexts.lookup agent = some .externalAgent then
      if clean : before.machine.machine.violations.IsEmpty then
        match projected : before.callProtocol? with
        | none => none
        | some beforeProtocol =>
            match issued : CallProtocol.handoff? beforeProtocol caller agent request loans with
            | none => none
            | some (call, afterProtocol) => some
                { caller, control, callerRegistered, agentRegistered, clean,
                  beforeProtocol, projected, call, afterProtocol, issued }
      else none else none else none
  | .pending .. | .terminal => none

namespace Entry

variable {before : ExecutionState.State ApiRequest} {request : ApiRequest}
  {loans : List CallProtocol.LoanRequest} {agent : ContextId}

/-- The carrier immediately after this bookkeeping handoff. -/
def after (entry : Entry before request loans agent) : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol entry.afterProtocol
    { before.machine with machine := entry.afterProtocol.machine } rfl
    (.pending entry.call entry.caller agent)

/-- The exact heterogeneous pending record minted by the successful handoff. -/
def pendingRecord (entry : Entry before request loans agent) : CallProtocol.Pending ApiRequest :=
  ⟨entry.caller, agent, request,
    (GrantMint.mint entry.beforeProtocol.grantSupply
      (loans.map (fun loan => loan.grant entry.caller agent))).1⟩

theorem after_projected (entry : Entry before request loans agent) :
    entry.after.callProtocol? = some entry.afterProtocol :=
  ExecutionState.State.ofCallProtocol_callProtocol? _ _ _ _

theorem recorded (entry : Entry before request loans agent) :
    entry.afterProtocol.pending.lookup entry.call = some entry.pendingRecord :=
  (CallProtocol.handoff?_records entry.issued).2.2.2.1

/-- `pending_exact` identifies the full pending table with this exact insertion. -/
theorem pending_exact (entry : Entry before request loans agent) :
    entry.afterProtocol.pending = entry.beforeProtocol.pending.insert entry.call entry.pendingRecord :=
  CallProtocol.handoff?_pending entry.issued

/-- The record is constructed from the exact caller, agent, request, and mint. -/
theorem record_fields (entry : Entry before request loans agent) :
    entry.pendingRecord.caller = entry.caller ∧
      entry.pendingRecord.agent = agent ∧
      entry.pendingRecord.request = request ∧
      entry.pendingRecord.loans =
        (GrantMint.mint entry.beforeProtocol.grantSupply
          (loans.map (fun loan => loan.grant entry.caller agent))).1 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem other_pending (entry : Entry before request loans agent) {other : CallProtocol.CallId}
    (different : other ≠ entry.call) :
    entry.afterProtocol.pending.lookup other = entry.beforeProtocol.pending.lookup other := by
  rw [entry.pending_exact]
  exact FiniteMap.lookup_insert_ne _ different _

theorem fresh (entry : Entry before request loans agent) :
    entry.beforeProtocol.pending.lookup entry.call = none :=
  CallProtocol.handoff?_fresh entry.issued

theorem storage_unchanged (entry : Entry before request loans agent) :
    entry.afterProtocol.machine.memory.allocations = before.machine.machine.memory.allocations ∧
    entry.afterProtocol.machine.memory.backings = before.machine.machine.memory.backings := by
  obtain ⟨memory, issued, machine⟩ := (CallProtocol.handoff?_records entry.issued).2.2.2.2.2
  have projected := (ExecutionState.State.callProtocol?_fields entry.projected).1
  rw [machine]
  exact ⟨(LoanBatch.allocations_issue? issued).trans
      (congrArg (fun machine => machine.memory.allocations) projected),
    (LoanBatch.backings_issue? issued).trans
      (congrArg (fun machine => machine.memory.backings) projected)⟩

theorem clean_after (entry : Entry before request loans agent) :
    entry.after.machine.machine.violations.IsEmpty := by
  obtain ⟨_, _, machine⟩ := (CallProtocol.handoff?_records entry.issued).2.2.2.2.2
  have projected := (ExecutionState.State.callProtocol?_fields entry.projected).1
  change entry.afterProtocol.machine.violations.IsEmpty
  rw [machine, projected]
  exact entry.clean

theorem after_control_consistent (entry : Entry before request loans agent) :
    entry.after.ControlConsistent := by
  obtain ⟨_, _, machine⟩ := (CallProtocol.handoff?_records entry.issued).2.2.2.2.2
  have projected := (ExecutionState.State.callProtocol?_fields entry.projected).1
  refine ⟨entry.afterProtocol, entry.after_projected, ⟨.thread, ?_⟩,
    ⟨.externalAgent, ?_⟩, entry.pendingRecord, entry.recorded, rfl, rfl⟩
  · rw [machine, projected]
    exact entry.callerRegistered
  · rw [machine, projected]
    exact entry.agentRegistered

end Entry
end Grass.Platform.Win32.ProtocolEntry
