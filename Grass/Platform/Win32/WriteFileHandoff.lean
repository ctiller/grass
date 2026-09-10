import Grass.Platform.Win32.WriteFile
import Grass.Platform.Win32.ProtocolEntry

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
abbrev EntryHandoff (before : ExecutionState.State ApiRequest) (request : Request)
    (abi : Abi.StackPlan before.machine request) (agent : ContextId) :=
  ProtocolEntry.Entry before (.writeFile request) (abi.loanPlan.requests request) agent

/-- Execute the checked boundary only from caller control with registered
contexts. Failure remains a refusal; it does not become a successful API call. -/
def entryHandoff? (before : ExecutionState.State ApiRequest) (request : Request)
    (abi : Abi.StackPlan before.machine request) (agent : ContextId) :
    Option (EntryHandoff before request abi agent) :=
  ProtocolEntry.issue? before (.writeFile request) (abi.loanPlan.requests request) agent

namespace EntryHandoff

variable {before : ExecutionState.State ApiRequest} {request : Request}
  {abi : Abi.StackPlan before.machine request} {agent : ContextId}

/-- The canonical output retains the same registers, RIP and flags. Only the
checked protocol's machine and metadata change at this bookkeeping boundary. -/
def after (handoff : EntryHandoff before request abi agent) : ExecutionState.State ApiRequest :=
  ProtocolEntry.Entry.after handoff

/-- The typed view contains the exact identities minted by this handoff. -/
def record (handoff : EntryHandoff before request abi agent) : CallProtocol.Pending Request :=
  let pending := ProtocolEntry.Entry.pendingRecord handoff
  ⟨pending.caller, pending.agent, request, pending.loans⟩

/-- `record_embedded` identifies the typed view with the one canonical pending record. -/
theorem record_embedded (handoff : EntryHandoff before request abi agent) :
    embedPending handoff.record = ProtocolEntry.Entry.pendingRecord handoff := rfl

theorem after_projected (handoff : EntryHandoff before request abi agent) :
    handoff.after.callProtocol? = some handoff.afterProtocol :=
  ProtocolEntry.Entry.after_projected handoff

/-- The heterogeneous table stores this entire typed record under this CallId. -/
theorem recorded (handoff : EntryHandoff before request abi agent) :
    handoff.afterProtocol.pending.lookup handoff.call = some (embedPending handoff.record) :=
  ProtocolEntry.Entry.recorded handoff

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
    handoff.afterProtocol.machine.memory.backings = before.machine.machine.memory.backings :=
  ProtocolEntry.Entry.storage_unchanged handoff

/-- The actual handoff begins the provider prefix at zero accepted output. -/
def initialPrefix (handoff : EntryHandoff before request abi agent) :
    Prefix abi.loanPlan handoff.afterProtocol handoff.call handoff.record where
  pending := handoff.pendingAt
  prepared := abi.entry.prepared.transport handoff.storage_unchanged.1 handoff.storage_unchanged.2
  clean := ProtocolEntry.Entry.clean_after handoff
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
    handoff.after.ControlConsistent :=
  ProtocolEntry.Entry.after_control_consistent handoff

end EntryHandoff
end Grass.Platform.Win32.WriteFile
