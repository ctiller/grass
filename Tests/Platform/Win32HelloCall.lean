import Tests.Platform.Win32LoaderEntry
import Grass.Platform.Win32.GetStdHandleStackPlan
import Grass.ISA.X86.Execution.ComputationFactory
import Grass.ISA.X86.Execution.CallFactory
import Grass.ISA.X86.Execution.MemoryMoveFactory
import Grass.ISA.X86.Execution.CheckedStep
import Grass.Platform.Win32.CallResumeBinding

/-!
# Actual source-linked Hello prefix through GetStdHandle handoff

This fixture executes the unchanged checked-in source through loading, its
derived prologue and local initialization, the source-authored
`mov ecx, STD_OUTPUT_HANDLE`, and the first indirect CALL. The return-frame
slots are derived from that actual CALL result, then checked handoff uses the
external agent already registered by the loader environment. Initial protocol
metadata is retained through the CPU prefix. This stops before a provider
result or return and makes no native execution correspondence claim.
-/

namespace Grass.Tests.Win32HelloCall

open Grass.Artifact Grass.Core Grass.Memory Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Platform.Win32 Grass.Platform.Win32.Loader
open Grass.Platform.Win32.ExecutionState Grass.Op

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Execute exactly the generated initializer sequence, recomputing the fixed
Windows policy at every reached state and checking each fetched encoding
against its source-derived initializer entry. -/
def runInitializations {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    List Grass.Assembly.SourceInitialization.Entry → State → Option State
  | [], before => some before
  | expected :: rest, before =>
      match Cpu.policy? loaded before with
      | none => none
      | some policy =>
          match MemoryMoveFactory.memoryMove policy before with
          | .error _ => none
          | .ok initialized =>
              if initialized.fetched.dispatched.fetch.site.encoding = expected.store.encoding then
                runInitializations loaded rest initialized.execution.result
              else none

private def callerReady? (checked : ExecutionState.State ApiRequest) :
    Option { _proof : Unit // checked.ControlConsistent } :=
  match control : checked.control with
  | .caller caller =>
      match projected : checked.callProtocol? with
      | none => none
      | some protocol =>
          match registered : protocol.machine.contexts.lookup caller with
          | none => none
          | some kind =>
              if available : CallProtocol.callerPending protocol caller = false then
                some ⟨(), by
                  unfold ExecutionState.State.ControlConsistent
                  rw [control]
                  exact ⟨protocol, projected, ⟨kind, registered⟩, available⟩⟩
              else none
  | .pending .. | .terminal => none

/-- The concrete prefix retains its loaded image, original raw bookkeeping,
checked projection, and caller-ready evidence. -/
structure ActualPreCall where
  before : RawState
  checked : ExecutionState.State ApiRequest
  checkedExact : before.checked? = some checked
  callerReady : checked.ControlConsistent

private def actualBody := (Grass.Assembly.SourceInput.extractHelloSourceChars
  Grass.Tests.Assembly.SourceResolve.authored).toOption.get (by native_decide)
private def actualFrame := (Grass.Assembly.SourceFrame.derive? actualBody).get (by native_decide)
private def actualSplice := (Grass.Assembly.SourceSplice.derive? actualFrame 0).get (by native_decide)
private def actualPlan := Grass.Tests.Win32LoaderEntry.helloPlan?.get (by native_decide)
private def actualImage : ImageInput :=
  ⟨actualPlan, (PE.writeImage actualPlan).toHostBytes, rfl⟩
private def actualInputs := Grass.Tests.Win32LoaderEntry.inputsFor actualPlan
  (.fromList [.fromList [0x7ff01000, 0x7ff02000, 0x7ff03000]])
private def actualLoaded : LoadedImage actualImage actualInputs :=
  (initialize? actualImage actualInputs).get (by native_decide)

/-- Structured endpoint evidence retains the exact checked evaluator equation,
CALL receipt, existing raw handoff, and its runtime-bearing result. -/
structure ActualHandoff where
  preCall : ActualPreCall
  policy : CpuAccessPolicy
  selected : Cpu.policy? actualLoaded preCall.checked.machine = some policy
  flags : RegisterSemantics.Flags Bool
  called : CallFactory.Success policy preCall.checked.machine
  evaluated : CheckedExecution.normal policy preCall.checked.machine flags =
    some (.ok (.call called))
  entered : @GetStdHandle.RawCallHandoff actualImage actualInputs actualLoaded
    preCall.before called.fetched.after called.afterRead called.afterStore called.displacement
    actualInputs.independentContext
  receiptExact : HEq entered.receipt called.receipt

private theorem transportedContinuation {left right : State} (same : left = right)
    (plan : GetStdHandle.StackPlan left) :
    (same ▸ plan).continuation = plan.continuation := by cases same; rfl

private theorem transportedProvenance {left right : State} (same : left = right)
    (plan : GetStdHandle.StackPlan left) :
    (same ▸ plan).returnSlot.provenance = plan.returnSlot.provenance := by cases same; rfl

private theorem transportedRange {left right : State} (same : left = right)
    (plan : GetStdHandle.StackPlan left) :
    (same ▸ plan).returnSlot.range = plan.returnSlot.range := by cases same; rfl

def actualHandoff? : Option ActualHandoff := do
  if covered : CallProtocol.GrantSupplyCovers actualLoaded.initialState.machine.memory
      (FreshSupply.initial : FreshSupply GrantTag) then
    let protocol : CallProtocol.State ApiRequest :=
      CallProtocol.initial actualLoaded.initialState.machine .initial covered
    let initial := ExecutionState.State.ofCallProtocol protocol actualLoaded.initialState rfl
      (.caller actualInputs.thread)
    match Grass.Assembly.PrologueFactory.execute actualLoaded actualSplice.prologue
        actualLoaded.initialState with
    | .error _ => none
    | .ok ⟨afterPrologue, _⟩ =>
        match runInitializations actualLoaded actualSplice.initialization.entries afterPrologue with
        | none => none
        | some afterInitialization =>
            match Cpu.policy? actualLoaded afterInitialization with
            | none => none
            | some movePolicy =>
                match ComputationFactory.move movePolicy afterInitialization with
                | .error _ => none
                | .ok moved =>
                    let before := initial.raw.withMachine moved.result
                    match checkedExact : before.checked? with
                    | none => none
                    | some checked =>
                        match callerReady? checked with
                        | none => none
                        | some callerReady =>
                            match selected : Cpu.policy? actualLoaded checked.machine with
                            | none => none
                            | some policy =>
                                let flags := checked.machine.statusFlags
                                match evaluated : CheckedExecution.normal policy checked.machine flags with
                                | some (.ok (.call called)) =>
                                    let binding := CallEntry.CallPolicy.ofFactory selected called
                                    match planned : GetStdHandle.StackPlanFactory.deriveLoaded? binding with
                                    | .error _ => none
                                    | .ok stack =>
                                        match reachedExact : CallEntry.reachedCall? checked
                                            called.receipt with
                                        | none => none
                                        | some reached =>
                                            have reachedMachine :=
                                              (CallEntry.reachedCall?_fields reachedExact).1
                                            let abi : GetStdHandle.StackPlan reached.machine :=
                                              reachedMachine.symm ▸ stack
                                            match GetStdHandle.entryHandoff? reached abi
                                                actualInputs.independentContext with
                                            | none => none
                                            | some handoff =>
                                                if caller : handoff.caller = actualInputs.thread then
                                                  let entered : GetStdHandle.CallHandoff actualLoaded checked
                                                      called.receipt actualInputs.independentContext :=
                                                    { policy := binding
                                                      callerReady := callerReady.property
                                                      reached, reachedExact, abi
                                                      continuation := by
                                                        exact (transportedContinuation
                                                          reachedMachine.symm stack).trans
                                                          (GetStdHandle.StackPlanFactory.loaded_continuation_exact planned)
                                                      returnProvenance := by
                                                        exact (transportedProvenance
                                                          reachedMachine.symm stack).trans
                                                          (ReturnHome.StackPlanFactory.return_provenance_exact planned)
                                                      returnRange := by
                                                        exact (transportedRange
                                                          reachedMachine.symm stack).trans
                                                          (ReturnHome.StackPlanFactory.return_range_exact planned)
                                                      handoff, caller }
                                                  let raw : @GetStdHandle.RawCallHandoff actualImage actualInputs actualLoaded
                                                      before called.fetched.after called.afterRead
                                                      called.afterStore called.displacement
                                                      actualInputs.independentContext :=
                                                    { checked, checkedExact, receipt := called.receipt,
                                                      entered }
                                                  have rawReceipt : raw.receipt = called.receipt := rfl
                                                  some {
                                                    preCall := {
                                                      before := before, checked := checked
                                                      checkedExact := checkedExact
                                                      callerReady := callerReady.property }
                                                    policy := policy, selected := selected, flags := flags
                                                    called := called, evaluated := evaluated, entered := raw
                                                    receiptExact := heq_of_eq rawReceipt }
                                                else none
                                | _ => none
  else none

theorem ActualHandoff.runtime_exact (result : ActualHandoff) :
    result.entered.after.calls.lookup result.entered.entered.handoff.call =
      some (.getStdHandle result.entered.entered.frame) :=
  result.entered.after_call

/-- The actual entered CALL supplies both initial resume premises from its
fixed policy binding and computed runtime insertion. -/
theorem ActualHandoff.resume_inputs (result : ActualHandoff) :
    ProviderResume.PolicyBinding actualLoaded result.entered.receipt ∧
      ProviderResume.Link result.entered.after result.entered.entered.handoff.call
        (.getStdHandle result.entered.entered.frame) result.entered.entered.frame
        result.entered.receipt :=
  result.entered.entered.resumeInputs result.preCall.before.calls

/-- The complete checked prefix and deterministic frame-plan checks. Expected
values are obtained from the retained receipts and ABI definitions rather than
handwritten instruction bytes or stack offsets. -/
def actualPrefix? : Option Bool := actualHandoff?.map fun result =>
  let entered := result.entered.entered
  let abi := entered.abi
  let handoff := entered.handoff
  actualSplice.initialization.entries.length == 1 &&
    BitVec.setWidth 32 (result.preCall.checked.machine.gpr .rcx) ==
      StdHandleId.output.value &&
    abi.continuation == result.called.receipt.fetch.site.fallthroughRip &&
    abi.returnSlot.provenance == result.called.receipt.storeDescriptor.provenance &&
    abi.returnSlot.range == result.called.receipt.storeDescriptor.range &&
    abi.returnSlot.range.size == WriteFile.Abi.returnAddressBytes &&
    abi.homeSlot.provenance == abi.returnSlot.provenance &&
    abi.homeSlot.range.size == Grass.ABI.Win64.shadowSpaceBytes &&
    handoff.caller == actualInputs.thread &&
    handoff.after.control == .pending handoff.call actualInputs.thread
      actualInputs.independentContext

private def check (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError "actual Hello GetStdHandle CALL prefix refused")

#eval check (actualPrefix? == some true)
#eval check actualHandoff?.isSome

end Grass.Tests.Win32HelloCall
