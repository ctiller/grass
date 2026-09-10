import Grass.ISA.X86.Execution.CallNormal
import Grass.ISA.X86.Execution.FetchFactory
import Grass.ISA.X86.Execution.RunFactory

/-! # Constructive fetched RIP-relative indirect CALL execution -/

namespace Grass.ISA.X86.Execution.CallFactory

open Grass.Memory Grass.Op Grass.Std.Logical

inductive Failure where
  | fetch (reason : FetchFactory.Failure)
  | unsupported (reached : State) (instruction : Instruction)
  | missingData (reached : State) (address : MachineAddress)
  | dataAddress (reached : State) (reason : AddressPlanFailure)
  | read (reached : State) (descriptor : AccessDescriptor)
      (reason : RunFactory.AccessFailure descriptor)
  | stackUnderflow (reached : State)
  | stackAddress (reached : State) (reason : AddressPlanFailure)
  | store (reached : State) (descriptor : AccessDescriptor)
      (reason : RunFactory.AccessFailure descriptor)

structure Success (policy : CpuAccessPolicy) (before : State) where
  displacement : BitVec 32
  fetched : FetchFactory.Success policy before
  afterRead : MachineState
  afterStore : MachineState
  receipt : CallNormal before fetched.after afterRead afterStore displacement
  fetch_exact : receipt.fetch = fetched.dispatched.fetch
  data_selected : policy.data
    (receipt.fetch.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt) 8 =
      some receipt.readDescriptor.provenance
  stack_provenance : receipt.storeDescriptor.provenance = policy.stack

namespace Success

def result {policy : CpuAccessPolicy} {before : State} (success : Success policy before) : State :=
  success.receipt.result

end Success

/-- From an actual fetch, execute the target read and return-address store for the
production RIP-relative indirect CALL form. -/
def callFromFetched {policy : CpuAccessPolicy} (before : State)
    (fetched : FetchFactory.Success policy before) : Except Failure (Success policy before) :=
      let site := fetched.dispatched.fetch
      match selected : fetched.dispatched.selection.instruction with
      | .callRip displacement =>
          let targetAddress := site.site.fallthroughRip + BitVec.ofInt 64 displacement.toInt
          match dataProvenance : policy.data targetAddress 8 with
          | none => .error (.missingData { before with machine := fetched.after } targetAddress)
          | some provenance =>
              match readPlan : planAddress fetched.after.memory provenance targetAddress with
              | .error reason =>
                  .error (.dataAddress { before with machine := fetched.after } reason)
              | .ok plan =>
                  let readDescriptor := plan.descriptor policy .dataRead 8
                  let readPolicy : StepPolicy :=
                    { site.run.policy with
                      oracle := Oracle.ofMemory (fun _ _ => []) (fun _ _ _ => 0) }
                  match readResult : RunFactory.access readPolicy fetched.after readDescriptor
                      site.run.context site.run.contextKind site.run.cause with
                  | .error reason =>
                      .error (.read
                        (RunFactory.AccessFailure.reached { before with machine := fetched.after } reason)
                        readDescriptor reason)
                  | .ok readSuccess =>
                      let read : ReadValue64 readSuccess.run :=
                        { writeData := fun _ _ => []
                          indeterminate := fun _ _ _ => 0
                          memoryOracle := by rw [readSuccess.policy_exact]
                          reads := rfl
                          writes := rfl
                          width := rfl
                          initialization := rfl }
                      if stackBound : 8 ≤ (before.gpr .rsp).toNat then
                        let stackAddress := before.gpr .rsp - 8
                        match stackPlan : planAddress readSuccess.after.memory policy.stack stackAddress with
                        | .error reason =>
                            .error (.stackAddress { before with machine := readSuccess.after } reason)
                        | .ok storePlan =>
                            let storeDescriptor := storePlan.descriptor policy .stackWrite 8
                            let storePolicy : StepPolicy :=
                              { readSuccess.run.policy with
                                oracle := Oracle.ofMemory
                                  (fun _ _ => le64 site.site.fallthroughRip) (fun _ _ _ => 0) }
                            match storeResult : RunFactory.access storePolicy readSuccess.after
                                storeDescriptor readSuccess.run.context
                                readSuccess.run.contextKind readSuccess.run.cause with
                            | .error reason =>
                                .error (.store
                                  (RunFactory.AccessFailure.reached
                                    { before with machine := readSuccess.after } reason)
                                  storeDescriptor reason)
                            | .ok storeSuccess =>
                                have metadata := fetched.observed.dispatch_metadata
                                  fetched.dispatched fetched.dispatch_exact
                                have fetchContext : site.descriptor.context = site.run.context := by
                                  calc
                                    site.descriptor.context =
                                        fetched.observed.descriptor.context :=
                                      congrArg AccessDescriptor.context metadata.2.2.2.2
                                    _ = policy.context := fetched.descriptorContext
                                    _ = fetched.observed.run.context := fetched.context_exact.symm
                                    _ = site.run.context := metadata.2.1.symm
                                have fetchSpace : site.descriptor.space = .cpuVirtual := by
                                  rw [metadata.2.2.2.2, fetched.descriptor_exact]
                                  rfl
                                have readAllocation : readSuccess.run.resolved.allocation =
                                    plan.allocation := by
                                  exact Option.some.inj
                                    (readSuccess.run.resolved.allocationLookup.symm.trans plan.lookup)
                                have storeAllocation : storeSuccess.run.resolved.allocation =
                                    storePlan.allocation := by
                                  exact Option.some.inj
                                    (storeSuccess.run.resolved.allocationLookup.symm.trans
                                      storePlan.lookup)
                                let receipt : CallNormal before fetched.after readSuccess.after
                                    storeSuccess.after displacement :=
                                  { fetch := site
                                    encoding := by
                                      have exact := fetched.dispatched.selection.encoding_eq
                                      rw [selected] at exact
                                      simpa [Instruction.encoding?] using exact
                                    readDescriptor := readDescriptor
                                    readRun := readSuccess.run
                                    read := read
                                    readPolicy := by rw [readSuccess.policy_exact]
                                    readContext := readSuccess.context_exact
                                    readContextKind := readSuccess.contextKind_exact
                                    readCause := readSuccess.cause_exact
                                    fetchContext := fetchContext
                                    fetchSpace := fetchSpace
                                    readDescriptorContext := by
                                      calc
                                        readDescriptor.context = policy.context := rfl
                                        _ = site.run.context :=
                                          (metadata.2.1.trans fetched.context_exact).symm
                                        _ = readSuccess.run.context :=
                                          readSuccess.context_exact.symm
                                    readIntent := rfl
                                    readSpace := rfl
                                    readOrdering := rfl
                                    readLedgerEffect := rfl
                                    readAuthorityEffect := rfl
                                    readAddress := rfl
                                    readPlaced := ⟨plan.base, by
                                      rw [readAllocation]
                                      exact plan.placed⟩
                                    storeDescriptor := storeDescriptor
                                    storeRun := storeSuccess.run
                                    storePolicy := by rw [storeSuccess.policy_exact]
                                    storeContext := storeSuccess.context_exact
                                    storeContextKind := storeSuccess.contextKind_exact
                                    storeCause := storeSuccess.cause_exact
                                    storeDescriptorContext := by
                                      calc
                                        storeDescriptor.context = policy.context := rfl
                                        _ = site.run.context :=
                                          (metadata.2.1.trans fetched.context_exact).symm
                                        _ = readSuccess.run.context :=
                                          readSuccess.context_exact.symm
                                        _ = storeSuccess.run.context :=
                                          storeSuccess.context_exact.symm
                                    storeOracle := by rw [storeSuccess.policy_exact]
                                    storeIntent := rfl
                                    storeSpace := rfl
                                    storeInitialization := rfl
                                    storeOrdering := rfl
                                    storeWidth := rfl
                                    storeInitialized := rfl
                                    storeLedgerEffect := rfl
                                    storeAuthorityEffect := rfl
                                    stackNoUnderflow := stackBound
                                    storeAddress := rfl
                                    storePlaced := ⟨storePlan.base, by
                                      rw [storeAllocation]
                                      exact storePlan.placed⟩ }
                                .ok
                                  { displacement := displacement
                                    fetched := fetched
                                    afterRead := readSuccess.after
                                    afterStore := storeSuccess.after
                                    receipt := receipt
                                    fetch_exact := rfl
                                    data_selected := by
                                      simpa [receipt, readDescriptor, targetAddress,
                                        AddressPlan.descriptor] using dataProvenance
                                    stack_provenance := rfl }
                      else .error (.stackUnderflow { before with machine := readSuccess.after })
      | instruction =>
          .error (.unsupported { before with machine := fetched.after } instruction)

def call (policy : CpuAccessPolicy) (before : State) : Except Failure (Success policy before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched => callFromFetched before fetched

end Grass.ISA.X86.Execution.CallFactory
