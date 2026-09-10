import Grass.Platform.Win32.WriteFileCall
import Grass.Platform.Win32.RawState

/-!
# Register-only ExitProcess entry

This checked initializer records the low DWORD of RCX at an actual reached
CALL and issues no memory loans. The empty batch describes only this selected
register-only entry slice, not native DLL teardown or other provider actions.
It neither observes process termination nor invents a return frame.
-/

namespace Grass.Platform.Win32.ExitProcess

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86
open Grass.Platform.Win32.Loader

/-- The DWORD argument at the Win64 first integer argument register. -/
def status (state : Execution.State) : BitVec 32 :=
  BitVec.setWidth 32 (state.gpr .rcx)

/-- Actual checked issuance for this register-only endpoint slice. -/
structure EntryHandoff (before : ExecutionState.State ApiRequest) (agent : ContextId) where
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
    (.exitProcess (status before.machine)) [] = some (call, afterProtocol)

/-- Run the actual protocol check, retaining its failure as a refusal. -/
def entryHandoff? (before : ExecutionState.State ApiRequest) (agent : ContextId) :
    Option (EntryHandoff before agent) :=
  match control : before.control with
  | .caller caller =>
      if callerRegistered : before.machine.machine.contexts.lookup caller = some .thread then
      if agentRegistered : before.machine.machine.contexts.lookup agent = some .externalAgent then
      if clean : before.machine.machine.violations.IsEmpty then
        match projected : before.callProtocol? with
        | none => none
        | some beforeProtocol =>
            match issued : CallProtocol.handoff? beforeProtocol caller agent
                (.exitProcess (status before.machine)) [] with
            | none => none
            | some (call, afterProtocol) => some
                { caller, control, callerRegistered, agentRegistered, clean,
                  beforeProtocol, projected, call, afterProtocol, issued }
      else none else none else none
  | .pending .. | .terminal => none

namespace EntryHandoff

variable {before : ExecutionState.State ApiRequest} {agent : ContextId}

/-- Retain the reached registers and exact protocol result under pending control. -/
def after (handoff : EntryHandoff before agent) : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol handoff.afterProtocol
    { before.machine with machine := handoff.afterProtocol.machine } rfl
    (.pending handoff.call handoff.caller agent)

/-- Keep all existing per-call data and insert only the newly issued occurrence. -/
def initRaw (handoff : EntryHandoff before agent) (calls : CallRuntimeTable) :
    ExecutionState.RawState :=
  handoff.after.raw (calls.insert handoff.call .exitProcess)

theorem recorded (handoff : EntryHandoff before agent) :
    handoff.afterProtocol.pending.lookup handoff.call =
      some ⟨handoff.caller, agent, .exitProcess (status before.machine),
        (Grass.Memory.GrantMint.mint handoff.beforeProtocol.grantSupply []).1⟩ :=
  (CallProtocol.handoff?_records handoff.issued).2.2.2.1

theorem runtime_exact (handoff : EntryHandoff before agent) (calls : CallRuntimeTable) :
    (handoff.initRaw calls).calls.lookup handoff.call = some .exitProcess :=
  Grass.Std.Logical.FiniteMap.lookup_insert_self _ _ _

theorem other_runtime (handoff : EntryHandoff before agent) (calls : CallRuntimeTable)
    {other : CallProtocol.CallId} (different : other ≠ handoff.call) :
    (handoff.initRaw calls).calls.lookup other = calls.lookup other :=
  Grass.Std.Logical.FiniteMap.lookup_insert_ne _ different _

theorem control_pending (handoff : EntryHandoff before agent) (calls : CallRuntimeTable) :
    (handoff.initRaw calls).control = .pending handoff.call handoff.caller agent := rfl

theorem status_exact (handoff : EntryHandoff before agent) (calls : CallRuntimeTable) :
    status (handoff.initRaw calls).machine = status before.machine := rfl

end EntryHandoff

/-- Bind entry issuance to the actual fixed-policy CALL and its exact reached
carrier. Native target identity and terminal correspondence remain separate. -/
structure CallHandoff {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (before : ExecutionState.State ApiRequest)
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    (receipt : Execution.CallNormal before.machine afterFetch afterRead afterStore displacement)
    (agent : ContextId) where
  policy : WriteFile.CallPolicy loaded receipt
  callerReady : before.ControlConsistent
  reached : ExecutionState.State ApiRequest
  reachedExact : WriteFile.reachedCall? before receipt = some reached
  handoff : EntryHandoff reached agent
  caller : handoff.caller = inputs.thread

end Grass.Platform.Win32.ExitProcess
