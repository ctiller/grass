import Grass.Platform.Win32.ConsoleEnvironment
import Grass.Platform.Win32.RawStep
import Grass.Platform.Win32.CallResumeBinding

/-!
# Observed GetStdHandle provider result

This bounded branch records a supplied post-provider general-register and
RFLAGS observation.  It performs no modeled memory step, physical return, or
native provider execution claim.  Its finite GPR checks cover the modeled Win64
nonvolatile vocabulary only; XMM, MXCSR, x87, and complete ABI coverage remain
outside this leaf.
-/

namespace Grass.Platform.Win32.GetStdHandle.ProviderResult

open Grass.ABI Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- Why a supplied provider register observation is not accepted. -/
inductive Failure where
  | caller
  | provider
  | rsp
  | nonvolatile
  | handle
  | dispatch
  | request
deriving Repr

/-- The finite modeled preservation check, excluding RSP which has its own
exact check. -/
def nonvolatileSame (initial observed : Gpr → BitVec 64) : Bool :=
  Win64.nonvolatileRegisters.all fun register =>
    if register = .rsp then true else observed register == initial register

/-- Start with the exact entered raw carrier, retaining its runtime table and
protocol data, then replace only GPRs and RFLAGS with the supplied observation. -/
def stage {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (prior : CallRuntimeTable) (gpr : Gpr → BitVec 64) (rflags : BitVec 64) : RawState :=
  { entered.afterRaw prior with
    machine := { (entered.afterRaw prior).machine with gpr := gpr, rflags := rflags } }

@[simp] theorem stage_rAX {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (prior : CallRuntimeTable) (gpr : Gpr → BitVec 64) (rflags : BitVec 64) :
    (stage entered prior gpr rflags).machine.gpr .rax = gpr .rax := rfl

@[simp] theorem stage_memory {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (prior : CallRuntimeTable) (gpr : Gpr → BitVec 64) (rflags : BitVec 64) :
    (stage entered prior gpr rflags).machine.machine = (entered.afterRaw prior).machine.machine := rfl

@[simp] theorem stage_metadata {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (prior : CallRuntimeTable) (gpr : Gpr → BitVec 64) (rflags : BitVec 64) :
    (stage entered prior gpr rflags).metadata = (entered.afterRaw prior).metadata := rfl

@[simp] theorem stage_control {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (prior : CallRuntimeTable) (gpr : Gpr → BitVec 64) (rflags : BitVec 64) :
    (stage entered prior gpr rflags).control = (entered.afterRaw prior).control := rfl

@[simp] theorem stage_calls {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (prior : CallRuntimeTable) (gpr : Gpr → BitVec 64) (rflags : BitVec 64) :
    (stage entered prior gpr rflags).calls = (entered.afterRaw prior).calls := rfl

/-- The unchanged represented machine permits the original handoff protocol
state to pack against the staged raw carrier. -/
theorem stage_pack {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (prior : CallRuntimeTable) (gpr : Gpr → BitVec 64) (rflags : BitVec 64) :
    (stage entered prior gpr rflags).metadata.pack?
      (stage entered prior gpr rflags).machine.machine = some entered.handoff.afterProtocol := by
  exact entered.handoff.after_projected

/-- Accepted observation receipt, indexed by the actual evaluated CALL that
produced the entry handoff. -/
structure Receipt {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (environment : ConsoleEnvironment)
    {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (evaluated : Raw.EvaluatedCall loaded before receipt) (prior : CallRuntimeTable)
    (gpr : Gpr → BitVec 64) (rflags : BitVec 64) where
  caller : environment.caller = entered.handoff.caller
  provider : environment.provider = agent
  rsp : gpr .rsp = entered.reached.machine.gpr .rsp
  nonvolatile : nonvolatileSame entered.reached.machine.gpr gpr = true
  handle : environment.getStdAllowed (GetStdHandle.selector entered.reached.machine) (gpr .rax)
  dispatch : ApiDispatch.Binding loaded
    (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt) receipt.read.value
  selected : ApiDispatch.select? loaded
    (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt)
    receipt.read.value = some dispatch
  request : dispatch.MatchesRequest (.getStdHandle (GetStdHandle.selector entered.reached.machine))

/-- Check the fixed observed-register branch. -/
def observe? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (environment : ConsoleEnvironment)
    {before : ExecutionState.State ApiRequest}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
    {agent : ContextId} (entered : GetStdHandle.CallHandoff loaded before receipt agent)
    (evaluated : Raw.EvaluatedCall loaded before receipt) (prior : CallRuntimeTable)
    (gpr : Gpr → BitVec 64) (rflags : BitVec 64) :
    Except Failure (Receipt loaded environment entered evaluated prior gpr rflags) :=
  if caller : environment.caller = entered.handoff.caller then
  if provider : environment.provider = agent then
  if rsp : gpr .rsp = entered.reached.machine.gpr .rsp then
  if nonvolatile : nonvolatileSame entered.reached.machine.gpr gpr = true then
  if handle : environment.getStdAllowed (GetStdHandle.selector entered.reached.machine) (gpr .rax) then
    match selected : ApiDispatch.select? loaded
        (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt) receipt.read.value with
    | none => .error .dispatch
    | some dispatch =>
        if api : dispatch.api = .getStdHandle then
          .ok ⟨caller, provider, rsp, nonvolatile, handle, dispatch, selected, api.symm⟩
        else .error .request
  else .error .handle
  else .error .nonvolatile
  else .error .rsp
  else .error .provider
  else .error .caller

namespace Receipt

variable {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
  {environment : ConsoleEnvironment} {before : ExecutionState.State ApiRequest}
  {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
  {receipt : CallNormal before.machine afterFetch afterRead afterStore displacement}
  {agent : ContextId} {entered : GetStdHandle.CallHandoff loaded before receipt agent}
  {evaluated : Raw.EvaluatedCall loaded before receipt} {prior : CallRuntimeTable}
  {gpr : Gpr → BitVec 64} {rflags : BitVec 64}

theorem nonvolatile_exact (observed : Receipt loaded environment entered evaluated prior gpr rflags)
    (register : Gpr) (member : register ∈ Win64.nonvolatileRegisters) (notRsp : register ≠ .rsp) :
    gpr register = entered.reached.machine.gpr register := by
  have checked := List.all_eq_true.mp observed.nonvolatile register member
  simp [notRsp] at checked
  exact checked

theorem resumeLink (_observed : Receipt loaded environment entered evaluated prior gpr rflags) :
    ProviderResume.Link (stage entered prior gpr rflags) entered.handoff.call
      (.getStdHandle entered.frame) entered.frame receipt := by
  have original := (entered.resumeInputs prior).2
  exact
    { runtimeLookup := by simp [stage]
      runtimeFrame := original.runtimeFrame
      entryRsp := original.entryRsp
      continuation := original.continuation
      returnProvenance := original.returnProvenance
      returnRange := original.returnRange }

theorem preservesNonvolatile (observed : Receipt loaded environment entered evaluated prior gpr rflags) :
    ProviderResume.PreservesNonvolatile (stage entered prior gpr rflags) entered.frame := by
  intro register
  change gpr register.val = entered.frame.saved register
  rw [observed.nonvolatile_exact register.val register.property.1 register.property.2]
  exact entered.frame_saved register

end Receipt
end Grass.Platform.Win32.GetStdHandle.ProviderResult
