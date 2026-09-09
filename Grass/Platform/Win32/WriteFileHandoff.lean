import Grass.Platform.Win32.WriteFile
import Grass.Platform.Win32.ExecutionState

/-!
# Checked full-batch WriteFile entry handoff

The input architectural state is the reached callee entry. This constructor
checks control, contexts and the full loan batch, and retains every unrelated
pending call. It does not prove that the CPU executed CALL: the caller must
connect this exact input and stack continuation to the actual instruction
receipt. No provider read or physical return is asserted by loan issuance.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical

/-- Receipt for the actual checked handoff of the semantic and derived ABI batch. -/
structure EntryHandoff (before : ExecutionState.State ApiRequest) (request : Request)
    (abi : Abi.StackPlan before.machine request) (agent : ContextId) where
  caller : ContextId
  control : before.control = .caller caller
  callerRegistered : before.machine.machine.contexts.lookup caller = some .thread
  agentRegistered : before.machine.machine.contexts.lookup agent = some .externalAgent
  clean : before.machine.machine.violations.IsEmpty
  beforeProtocol : ProtocolState
  projected : before.callProtocol? = some beforeProtocol
  call : CallProtocol.CallId
  afterProtocol : ProtocolState
  issued : CallProtocol.handoff? beforeProtocol caller agent (.writeFile request)
    (abi.loanPlan.requests request) = some (call, afterProtocol)

/-- Execute the checked boundary only from caller control with registered
contexts. Failure remains a refusal; it does not become a successful API call. -/
def entryHandoff? (before : ExecutionState.State ApiRequest) (request : Request)
    (abi : Abi.StackPlan before.machine request) (agent : ContextId) :
    Option (EntryHandoff before request abi agent) :=
  match control : before.control with
  | .caller caller =>
      if callerRegistered : before.machine.machine.contexts.lookup caller = some .thread then
      if agentRegistered : before.machine.machine.contexts.lookup agent = some .externalAgent then
      if clean : before.machine.machine.violations.IsEmpty then
        match projected : before.callProtocol? with
        | none => none
        | some beforeProtocol =>
            match issued : CallProtocol.handoff? beforeProtocol caller agent (.writeFile request)
                (abi.loanPlan.requests request) with
            | none => none
            | some (call, afterProtocol) => some
                { caller, control, callerRegistered, agentRegistered, clean
                  beforeProtocol, projected, call, afterProtocol, issued }
      else none else none else none
  | .pending .. | .terminal => none

namespace EntryHandoff

variable {before : ExecutionState.State ApiRequest} {request : Request}
  {abi : Abi.StackPlan before.machine request} {agent : ContextId}

/-- The canonical output retains the same registers, RIP and flags. Only the
checked protocol's machine and metadata change at this bookkeeping boundary. -/
def after (handoff : EntryHandoff before request abi agent) : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol handoff.afterProtocol
    { before.machine with machine := handoff.afterProtocol.machine } rfl
    (.pending handoff.call handoff.caller agent)

/-- The typed view contains the exact identities minted by this handoff. -/
def record (handoff : EntryHandoff before request abi agent) : CallProtocol.Pending Request :=
  ⟨handoff.caller, agent, request,
    (GrantMint.mint handoff.beforeProtocol.grantSupply
      ((abi.loanPlan.requests request).map (fun loan => loan.grant handoff.caller agent))).1⟩

theorem after_projected (handoff : EntryHandoff before request abi agent) :
    handoff.after.callProtocol? = some handoff.afterProtocol :=
  ExecutionState.State.ofCallProtocol_callProtocol? _ _ _ _

/-- The heterogeneous table stores this entire typed record under this CallId. -/
theorem recorded (handoff : EntryHandoff before request abi agent) :
    handoff.afterProtocol.pending.lookup handoff.call = some (embedPending handoff.record) :=
  (CallProtocol.handoff?_records handoff.issued).2.2.2.1

/-- Both portions refer to actual recorded grant IDs, with current custody. -/
theorem pendingAt (handoff : EntryHandoff before request abi agent) :
    PendingAt abi.loanPlan handoff.afterProtocol handoff.call handoff.record := by
  refine ⟨handoff.recorded, ?_, ?_⟩
  · exact embedPending_valid.mp
      (handoff.afterProtocol.pendingValid.2 _ (FiniteMap.mem_of_lookup handoff.recorded)).2
  · have partition := CallProtocol.handoff?_loanPartition handoff.issued handoff.recorded
    exact ⟨partition.grantsExact⟩

theorem storage_unchanged (handoff : EntryHandoff before request abi agent) :
    handoff.afterProtocol.machine.memory.allocations = before.machine.machine.memory.allocations ∧
    handoff.afterProtocol.machine.memory.backings = before.machine.machine.memory.backings := by
  obtain ⟨memory, issued, machine⟩ := (CallProtocol.handoff?_records handoff.issued).2.2.2.2.2
  have projected := (ExecutionState.State.callProtocol?_fields handoff.projected).1
  rw [machine]
  exact ⟨(LoanBatch.allocations_issue? issued).trans
      (congrArg (fun machine => machine.memory.allocations) projected),
    (LoanBatch.backings_issue? issued).trans
      (congrArg (fun machine => machine.memory.backings) projected)⟩

/-- The actual handoff begins the provider prefix at zero accepted output. -/
def initialPrefix (handoff : EntryHandoff before request abi agent) :
    Prefix abi.loanPlan handoff.afterProtocol handoff.call handoff.record where
  pending := handoff.pendingAt
  prepared := abi.entry.prepared.transport handoff.storage_unchanged.1 handoff.storage_unchanged.2
  clean := by
    obtain ⟨_, _, machine⟩ := (CallProtocol.handoff?_records handoff.issued).2.2.2.2.2
    rw [machine, (ExecutionState.State.callProtocol?_fields handoff.projected).1]
    exact handoff.clean
  accepted := 0
  bounded := Nat.zero_le _

/-- Causal entry evidence must describe this same actual full-batch handoff. -/
def history (handoff : EntryHandoff before request abi agent) (realization : Realization)
    (causal : HandoffCausality realization.causal handoff.call handoff.record
      handoff.beforeProtocol handoff.afterProtocol) :
    History abi.loanPlan realization handoff.beforeProtocol handoff.call handoff.record
      handoff.initialPrefix :=
  .handoff handoff.initialPrefix handoff.issued
    (by rw [(ExecutionState.State.callProtocol?_fields handoff.projected).1]
        exact abi.entry.prepared) causal rfl

/-- Caller control is suspended on the exact newly recorded occurrence. -/
theorem after_control_consistent (handoff : EntryHandoff before request abi agent) :
    handoff.after.ControlConsistent := by
  obtain ⟨_, _, machine⟩ := (CallProtocol.handoff?_records handoff.issued).2.2.2.2.2
  have projected := (ExecutionState.State.callProtocol?_fields handoff.projected).1
  refine ⟨handoff.afterProtocol, handoff.after_projected, ⟨.thread, ?_⟩,
    ⟨.externalAgent, ?_⟩, embedPending handoff.record, handoff.recorded, rfl, rfl⟩
  · rw [machine, projected]; exact handoff.callerRegistered
  · rw [machine, projected]; exact handoff.agentRegistered

end EntryHandoff
end Grass.Platform.Win32.WriteFile
