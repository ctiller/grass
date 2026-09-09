import Grass.Platform.Win32.RawState
import Grass.Platform.Win32.CpuPolicy
import Grass.Platform.Win32.WriteFileResult
import Grass.ISA.X86.Execution.ReturnSlotFactory

/-!
# Bounded Windows provider resume

This module performs the one architectural operation available at an opaque
provider boundary: an actual checked read of the return slot.  The provider has
no fetched `RET` byte in this model.  Consequently the resulting RIP and RSP
are a platform resume construction justified by the retained call frame, not
an x86 instruction receipt.

The Win64 facts used here are limited to the modeled general-purpose register
table in `Grass.ABI.Win64.Convention`.  XMM preservation, MXCSR, x87 control
state, and direction-flag adequacy remain outside the current state vocabulary.
-/

namespace Grass.Platform.Win32.ProviderResume

open Grass.Core Grass.Memory Grass.Op Grass.ABI Grass.ISA.X86
open Grass.ISA.X86.Execution Grass.Platform.Win32.Loader
open Grass.Platform.Win32.ExecutionState

/-- Project the return frame stored under a returning endpoint variant. -/
def returnFrame? : CallRuntime → Option ReturnFrame
  | .getStdHandle frame => some frame
  | .writeFile runtime => some runtime.toReturnFrame
  | .exitProcess => none

/-- Concrete data agreement between a call identity, its current runtime entry,
and a CALL receipt with the same frame coordinates. Endpoint issuance and
service receipts must additionally prove that this receipt is the call which
issued the retained entry; equal fields alone do not establish history. -/
structure Link {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32}
    (before : RawState) (callId : CallProtocol.CallId) (runtime : CallRuntime)
    (frame : ReturnFrame)
    (call : CallNormal callBefore afterFetch afterTarget afterCall displacement) : Prop where
  runtimeLookup : before.calls.lookup callId = some runtime
  runtimeFrame : returnFrame? runtime = some frame
  entryRsp : frame.entryRsp = call.result.gpr .rsp
  continuation : frame.continuation = call.fetch.site.fallthroughRip
  returnProvenance : frame.returnSlot.provenance = call.storeDescriptor.provenance
  returnRange : frame.returnSlot.range = call.storeDescriptor.range

/-- The fixed policy selected at the original CALL site is the policy carried
by that actual receipt. This is explicit evidence; selection alone does not
identify a separately supplied CALL receipt. -/
structure OriginalCallPolicy {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    (policy : CpuAccessPolicy)
    (call : CallNormal callBefore afterFetch afterTarget afterCall displacement) : Prop where
  selected : Cpu.policy? loaded callBefore = some policy
  operation : call.fetch.run.policy = policy.operationPolicy
  context : call.fetch.run.context = policy.context
  contextKind : call.fetch.run.contextKind = policy.contextKind
  cause : call.fetch.run.cause = policy.cause
  stack : call.storeDescriptor.provenance = policy.stack

/-- Endpoint evidence that whichever unique fixed policy is selected for the
original site agrees with the retained CALL receipt. -/
structure PolicyBinding {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    (call : CallNormal callBefore afterFetch afterTarget afterCall displacement) : Prop where
  agrees : ∀ {policy}, Cpu.policy? loaded callBefore = some policy →
    OriginalCallPolicy loaded policy call

/-- The modeled part of the provider's Win64 preservation obligation.  These
are observations of the actual reached provider state, never values assigned by
the resume constructor. -/
def PreservesNonvolatile (before : RawState) (frame : ReturnFrame) : Prop :=
  ∀ register : { r : Gpr // r ∈ Win64.nonvolatileRegisters ∧ r ≠ .rsp },
    before.machine.gpr register.val = frame.saved register

/-- WriteFile returns its raw 32-bit BOOL in the low half of RAX.  The Win64
boundary represented here does not constrain the upper half. -/
def WriteFileOutput (before : RawState) (result : WriteFile.ReturnResult) : Prop :=
  BitVec.setWidth 32 (before.machine.gpr .rax) = result.rawBool

/-- Change only the control coordinates supplied by the checked frame.  All
other GPRs and the provider's actual RFLAGS remain exactly as reached. -/
def resumedState (before : State) (target : BitVec 64) (afterRead : MachineState) : State :=
  { before with
    machine := afterRead
    gpr := fun register => if register = .rsp then
      before.gpr .rsp + BitVec.ofNat 64 WriteFile.Abi.returnAddressBytes
      else before.gpr register
    rip := target }

/-- A successful bounded resume retains the actual read receipt and all
authoritative identity/frame agreement. -/
structure Success {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs)
    {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32} (before : RawState) (callId : CallProtocol.CallId)
    (runtime : CallRuntime) (frame : ReturnFrame)
    (call : CallNormal callBefore afterFetch afterTarget afterCall displacement) where
  policy : CpuAccessPolicy
  originalPolicy : OriginalCallPolicy loaded policy call
  link : Link before callId runtime frame call
  preserved : PreservesNonvolatile before frame
  slot : ReturnSlotFactory.Success policy call before.machine
  after : RawState
  afterExact : after = { before with
    machine := resumedState before.machine slot.receipt.read.value slot.afterRead }

inductive Failure where
  | policyUnavailable (reached : RawState)
  | returnSlot (reason : ReturnSlotFactory.Failure)

/-- The architectural state retained by every return-slot refusal. -/
def returnSlotReached : ReturnSlotFactory.Failure → State
  | .address reached _ | .wrongSlot reached _ _ | .wrongContext reached => reached
  | .access reached _ _ | .targetMismatch reached _ _ => reached

/-- Reattach the original metadata, control, and runtime table to the exact
architectural state reached by a refusal. -/
def Failure.reached (before : RawState) : Failure → RawState
  | .policyUnavailable reached => reached
  | .returnSlot reason => { before with machine := returnSlotReached reason }

/-- Read the actual current slot using the fixed Windows policy.  Frame and
runtime evidence are inputs from the endpoint receipt; only policy selection
and the memory read are computed here. -/
def resume {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs)
    {callBefore : State} {afterFetch afterTarget afterCall : MachineState}
    {displacement : BitVec 32} (before : RawState) (callId : CallProtocol.CallId)
    (runtime : CallRuntime) (frame : ReturnFrame)
    (call : CallNormal callBefore afterFetch afterTarget afterCall displacement)
    (binding : PolicyBinding loaded call)
    (link : Link before callId runtime frame call)
    (preserved : PreservesNonvolatile before frame) :
    Except Failure (Success loaded before callId runtime frame call) :=
  match selected : Cpu.policy? loaded callBefore with
  | none => .error (.policyUnavailable before)
  | some policy =>
      match ReturnSlotFactory.read policy call before.machine with
      | .error reason => .error (.returnSlot reason)
      | .ok slot =>
          .ok { policy := policy, originalPolicy := binding.agrees selected, link := link
                preserved := preserved, slot := slot
                after := { before with
                  machine := resumedState before.machine slot.receipt.read.value slot.afterRead }
                afterExact := rfl }

namespace Success

theorem machine_afterRead {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call) :
    success.after.machine.machine = success.slot.afterRead := by
  rw [success.afterExact]
  rfl

theorem rip_exact {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call) :
    success.after.machine.rip = frame.continuation := by
  rw [success.afterExact]
  exact success.slot.receipt.target_exact.trans success.link.continuation.symm

theorem rsp_exact {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call) :
    success.after.machine.gpr .rsp =
      before.machine.gpr .rsp + BitVec.ofNat 64 WriteFile.Abi.returnAddressBytes := by
  rw [success.afterExact]
  simp [resumedState]

theorem rsp_frame {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call) :
    success.after.machine.gpr .rsp = frame.restoredRsp := by
  rw [success.rsp_exact, ReturnFrame.restoredRsp, success.link.entryRsp,
    call.rsp_exact]
  have restored := success.slot.receipt.restoredRsp
  change before.machine.gpr .rsp + 8 = callBefore.gpr .rsp at restored
  change before.machine.gpr .rsp + 8 = (callBefore.gpr .rsp - 8) + 8
  rw [restored]
  exact (BitVec.sub_add_cancel _ _).symm

theorem rsp_original {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call) :
    success.after.machine.gpr .rsp = callBefore.gpr .rsp := by
  rw [success.rsp_exact]
  change before.machine.gpr .rsp + 8 = callBefore.gpr .rsp
  exact success.slot.receipt.restoredRsp

theorem rflags_exact {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call) :
    success.after.machine.rflags = before.machine.rflags := by rw [success.afterExact]; rfl

theorem gpr_other {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call) (register : Gpr)
    (other : register ≠ .rsp) :
    success.after.machine.gpr register = before.machine.gpr register := by
  rw [success.afterExact]
  simp [resumedState, other]

theorem nonvolatile_exact {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call)
    (register : { r : Gpr // r ∈ Win64.nonvolatileRegisters ∧ r ≠ .rsp }) :
    success.after.machine.gpr register.val = frame.saved register :=
  (success.gpr_other register.val register.property.2).trans (success.preserved register)

theorem raw_frame {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call) :
    success.after.metadata = before.metadata ∧ success.after.control = before.control ∧
      success.after.calls = before.calls := by
  rw [success.afterExact]
  exact ⟨rfl, rfl, rfl⟩

theorem writeFile_output_retained {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {callBefore : State}
    {afterFetch afterTarget afterCall : MachineState} {displacement : BitVec 32}
    {before : RawState} {callId : CallProtocol.CallId} {runtime : CallRuntime}
    {frame : ReturnFrame} {call : CallNormal callBefore afterFetch afterTarget afterCall displacement}
    (success : Success loaded before callId runtime frame call)
    {result : WriteFile.ReturnResult} (output : WriteFileOutput before result) :
    BitVec.setWidth 32 (success.after.machine.gpr .rax) = result.rawBool :=
  (congrArg (BitVec.setWidth 32) (success.gpr_other .rax (by decide))).trans output

end Success
end Grass.Platform.Win32.ProviderResume
