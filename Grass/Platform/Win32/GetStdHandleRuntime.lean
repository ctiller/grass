import Grass.Platform.Win32.RawState
import Grass.Platform.Win32.WriteFileCall
import Grass.Platform.Win32.ReturnHome

/-!
# Checked GetStdHandle entry and runtime initialization

This boundary starts with an actual indirect CALL receipt.  It reads the
selector from the reached Win64 argument register, issues the complete return
and home-space loan batch, and records the resulting return frame under the
fresh protocol CallId.  It does not identify the indirect target as the native
export and makes no claim about a provider result or physical return.
-/

namespace Grass.Platform.Win32.GetStdHandle

open Grass.ABI Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86
open Grass.Platform.Win32.ExecutionState
open Grass.Platform.Win32.Loader

/-- The DWORD argument passed in RCX, obtained from the actual post-CALL state. -/
def selector (state : Execution.State) : BitVec 32 :=
  BitVec.setWidth 32 (state.gpr .rcx)

/-- GetStdHandle needs no semantic memory loans.  Its complete ABI batch is the
saved return address followed by writable Win64 home space. -/
def stackRequests (returnSlot homeSlot : WriteFile.Argument) :
    List CallProtocol.LoanRequest :=
  ReturnHome.stackRequests returnSlot homeSlot

/-- Resolved callee-entry stack coordinates used by the fixed handoff. -/
abbrev StackPlan := ReturnHome.Plan

def StackPlan.requests {state : Execution.State} (plan : StackPlan state) :
    List CallProtocol.LoanRequest :=
  stackRequests plan.returnSlot plan.homeSlot

/-- Checked protocol handoff for the selector and the complete ABI batch. -/
structure EntryHandoff (before : ExecutionState.State ApiRequest)
    (abi : StackPlan before.machine) (agent : ContextId) where
  caller : ContextId
  control : before.control = .caller caller
  callerRegistered : before.machine.machine.contexts.lookup caller = some .thread
  agentRegistered : before.machine.machine.contexts.lookup agent = some .externalAgent
  clean : before.machine.machine.violations.IsEmpty
  beforeProtocol : CallProtocol.State ApiRequest
  projected : before.callProtocol? = some beforeProtocol
  call : CallProtocol.CallId
  afterProtocol : CallProtocol.State ApiRequest
  issued : CallProtocol.handoff? beforeProtocol caller agent
    (.getStdHandle (selector before.machine)) abi.requests = some (call, afterProtocol)

/-- Run the fixed checked boundary. Refusal leaves the actual input available
to the caller and does not create a pending occurrence or runtime entry. -/
def entryHandoff? (before : ExecutionState.State ApiRequest)
    (abi : StackPlan before.machine) (agent : ContextId) :
    Option (EntryHandoff before abi agent) :=
  match control : before.control with
  | .caller caller =>
      if callerRegistered : before.machine.machine.contexts.lookup caller = some .thread then
      if agentRegistered : before.machine.machine.contexts.lookup agent = some .externalAgent then
      if clean : before.machine.machine.violations.IsEmpty then
        match projected : before.callProtocol? with
        | none => none
        | some beforeProtocol =>
            match issued : CallProtocol.handoff? beforeProtocol caller agent
                (.getStdHandle (selector before.machine)) abi.requests with
            | none => none
            | some (call, afterProtocol) => some
                { caller, control, callerRegistered, agentRegistered, clean,
                  beforeProtocol, projected, call, afterProtocol, issued }
      else none else none else none
  | .pending .. | .terminal => none

namespace EntryHandoff

variable {before : ExecutionState.State ApiRequest} {abi : StackPlan before.machine}
  {agent : ContextId}

def after (handoff : EntryHandoff before abi agent) : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol handoff.afterProtocol
    { before.machine with machine := handoff.afterProtocol.machine } rfl
    (.pending handoff.call handoff.caller agent)

def record (handoff : EntryHandoff before abi agent) : CallProtocol.Pending ApiRequest :=
  ⟨handoff.caller, agent, .getStdHandle (selector before.machine),
    (GrantMint.mint handoff.beforeProtocol.grantSupply
      (abi.requests.map (fun loan => loan.grant handoff.caller agent))).1⟩

theorem after_projected (handoff : EntryHandoff before abi agent) :
    handoff.after.callProtocol? = some handoff.afterProtocol :=
  ExecutionState.State.ofCallProtocol_callProtocol? _ _ _ _

theorem recorded (handoff : EntryHandoff before abi agent) :
    handoff.afterProtocol.pending.lookup handoff.call = some handoff.record :=
  (CallProtocol.handoff?_records handoff.issued).2.2.2.1

theorem storage_unchanged (handoff : EntryHandoff before abi agent) :
    handoff.afterProtocol.machine.memory.allocations = before.machine.machine.memory.allocations ∧
    handoff.afterProtocol.machine.memory.backings = before.machine.machine.memory.backings := by
  obtain ⟨memory, issued, machine⟩ := (CallProtocol.handoff?_records handoff.issued).2.2.2.2.2
  have projected := (ExecutionState.State.callProtocol?_fields handoff.projected).1
  rw [machine]
  exact ⟨(LoanBatch.allocations_issue? issued).trans
      (congrArg (fun machine => machine.memory.allocations) projected),
    (LoanBatch.backings_issue? issued).trans
      (congrArg (fun machine => machine.memory.backings) projected)⟩

end EntryHandoff

/-- Actual CALL, fixed Windows access policy, exact stack coordinates, and the
fresh GetStdHandle handoff. -/
structure CallHandoff {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (before : ExecutionState.State ApiRequest)
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement)
    (agent : ContextId) where
  policy : WriteFile.CallPolicy loaded receipt
  callerReady : before.ControlConsistent
  reached : ExecutionState.State ApiRequest
  reachedExact : WriteFile.reachedCall? before receipt = some reached
  abi : StackPlan reached.machine
  continuation : abi.continuation = receipt.fetch.site.fallthroughRip
  returnProvenance : abi.returnSlot.provenance = receipt.storeDescriptor.provenance
  returnRange : abi.returnSlot.range = receipt.storeDescriptor.range
  handoff : EntryHandoff reached abi agent
  caller : handoff.caller = inputs.thread

namespace CallHandoff

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {before : ExecutionState.State ApiRequest}
  {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
  {receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement}
  {agent : ContextId}

/-- Runtime data is projected only from the actual reached CALL and its ABI plan. -/
def frame (handoff : CallHandoff loaded before receipt agent) : ReturnFrame :=
  ReturnFrame.ofPlan handoff.abi

/-- Attach the fresh runtime entry while retaining every existing CallId. -/
def afterRaw (handoff : CallHandoff loaded before receipt agent)
    (calls : CallRuntimeTable) : RawState :=
  (handoff.handoff.after.raw calls).setCall handoff.handoff.call (.getStdHandle handoff.frame)

@[simp] theorem afterRaw_call (handoff : CallHandoff loaded before receipt agent)
    (calls : CallRuntimeTable) :
    (handoff.afterRaw calls).calls.lookup handoff.handoff.call =
      some (.getStdHandle handoff.frame) :=
  RawState.setCall_lookup _ _ _

theorem afterRaw_other (handoff : CallHandoff loaded before receipt agent)
    (calls : CallRuntimeTable) {other : CallProtocol.CallId}
    (different : other ≠ handoff.handoff.call) :
    (handoff.afterRaw calls).calls.lookup other = calls.lookup other :=
  RawState.setCall_other _ different _

@[simp] theorem frame_entryRsp (handoff : CallHandoff loaded before receipt agent) :
    handoff.frame.entryRsp = handoff.reached.machine.gpr .rsp := rfl

theorem frame_continuation (handoff : CallHandoff loaded before receipt agent) :
    handoff.frame.continuation = receipt.fetch.site.fallthroughRip :=
  handoff.continuation

@[simp] theorem frame_saved (handoff : CallHandoff loaded before receipt agent)
    (register : { r : Gpr // r ∈ Win64.nonvolatileRegisters ∧ r ≠ .rsp }) :
    handoff.frame.saved register = handoff.reached.machine.gpr register.val := rfl

theorem selector_exact (handoff : CallHandoff loaded before receipt agent) :
    handoff.handoff.record.request =
      .getStdHandle (BitVec.setWidth 32 (receipt.result.gpr .rcx)) := by
  have reached := (WriteFile.reachedCall?_fields handoff.reachedExact).1
  simp [EntryHandoff.record, selector, reached]

end CallHandoff

/-- The combined raw boundary retains the actual pre-CALL carrier.  The CALL
receipt is indexed by its successful checked projection, and the output uses
that raw carrier's exact pre-existing runtime table. -/
structure RawCallHandoff {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (before : RawState)
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (agent : ContextId) where
  checked : ExecutionState.State ApiRequest
  checkedExact : before.checked? = some checked
  receipt : Execution.CallNormal checked.machine afterFetch afterRead afterStore displacement
  entered : CallHandoff loaded checked receipt agent

namespace RawCallHandoff

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {before : RawState} {afterFetch afterRead afterStore : MachineState}
  {displacement : BitVec 32} {agent : ContextId}

/-- One raw result for the combined actual CALL, protocol handoff, and runtime
capture. No intermediate raw state needs to retain the CALL receipt. -/
def after (handoff : @RawCallHandoff image inputs loaded before afterFetch afterRead
    afterStore displacement agent) : RawState :=
  handoff.entered.afterRaw before.calls

@[simp] theorem after_call (handoff : @RawCallHandoff image inputs loaded before afterFetch
    afterRead afterStore displacement agent) :
    handoff.after.calls.lookup handoff.entered.handoff.call =
      some (CallRuntime.getStdHandle handoff.entered.frame) := by
  exact handoff.entered.afterRaw_call before.calls

theorem after_other (handoff : @RawCallHandoff image inputs loaded before afterFetch afterRead
    afterStore displacement agent)
    {other : CallProtocol.CallId}
    (different : other ≠ handoff.entered.handoff.call) :
    handoff.after.calls.lookup other = before.calls.lookup other :=
  handoff.entered.afterRaw_other before.calls different

theorem checked_is_exact_preCall
    (handoff : @RawCallHandoff image inputs loaded before afterFetch afterRead afterStore
      displacement agent) :
    handoff.checked.raw before.calls = before :=
  RawState.checked?_raw handoff.checkedExact

end RawCallHandoff
end Grass.Platform.Win32.GetStdHandle
