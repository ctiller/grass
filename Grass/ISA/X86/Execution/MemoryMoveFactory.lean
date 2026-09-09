import Grass.ISA.X86.Execution.MemoryMoveSelection
import Grass.ISA.X86.Execution.AccessPolicy
import Grass.ISA.X86.Execution.RunFactory
import Grass.ISA.X86.Execution.FetchFactory

namespace Grass.ISA.X86.Execution.MemoryMoveFactory

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86 MemoryMoveNormal

inductive Failure where
  | fetch (reason : FetchFactory.Failure)
  | unsupported (reached : State) (encoding : InsnEncoding)
  | address (reached : State) (reason : AddressPlanFailure)
  | access (reached : State) (descriptor : AccessDescriptor)
      (reason : RunFactory.AccessFailure descriptor)

inductive Success {before : State} {afterFetch : MachineState}
    (fetch : FetchedSite before afterFetch) where
  | store {instruction} (encoded : Instruction.Encoding instruction) {afterData}
      (receipt : StoreNormal instruction encoded before afterFetch afterData)
      (fetch_exact : receipt.fetch = fetch) : Success fetch
  | load {instruction} (encoded : Instruction.Encoding instruction) {afterData}
      (receipt : LoadNormal instruction encoded before afterFetch afterData)
      (fetch_exact : receipt.fetch = fetch) : Success fetch

namespace Success

def result {before : State} {afterFetch : MachineState} {fetch : FetchedSite before afterFetch} :
    Success fetch → State
  | .store _ receipt _ => receipt.result
  | .load _ receipt _ => receipt.result

end Success

private def reached (before : State) {d : AccessDescriptor} :
    RunFactory.AccessFailure d → State
  | .rejected _ => before
  | .violations after | .preparationUnavailable after _ | .answerUnavailable after =>
      { before with machine := after }

/-- Internal leaf used by the fixed FetchFactory wrapper; all execution metadata is explicit. -/
private def fromSite (policy : CpuAccessPolicy) {before : State} {afterFetch : MachineState}
    (fetch : FetchedSite before afterFetch)
    (fetchSpace : fetch.descriptor.space = .cpuVirtual)
    (fetchContext : fetch.descriptor.context = fetch.run.context)
    (policyContext : policy.context = fetch.run.context) : Except Failure (Success fetch) :=
  match MemoryMoveSelection.select fetch.site.encoding with
  | none => .error (Failure.unsupported { before with machine := afterFetch } fetch.site.encoding)
  | some selected =>
      let address := Instruction.effectiveAddress before selected.instruction
      match planAddress afterFetch.memory policy.stack address with
      | .error reason => .error (Failure.address { before with machine := afterFetch } reason)
      | .ok plan =>
          let purpose := match selected.instruction with
            | .load32 _ _ => AccessPurpose.stackRead | _ => .stackWrite
          let descriptor := plan.descriptor policy purpose selected.instruction.width
          let writeData : MachineState → AccessDescriptor → Grass.Std.Logical.ByteSeq :=
            fun _ _ => selected.instruction.payload?.getD []
          let indeterminate : MachineState → (d : AccessDescriptor) → Nat →
              Grass.Std.Logical.Byte :=
            fun _ _ _ => 0
          let dataPolicy : StepPolicy :=
            { fetch.run.policy with oracle := Oracle.ofMemory writeData indeterminate }
          match RunFactory.access dataPolicy afterFetch descriptor fetch.run.context
              fetch.run.contextKind fetch.run.cause with
          | .error reason => .error (Failure.access
              (reached { before with machine := afterFetch } reason) descriptor reason)
          | .ok result =>
              let access : MemoryAccess fetch result.after :=
                { descriptor := descriptor, run := result.run
                  policy := by rw [result.policy_exact]
                  writeData := writeData, indeterminate := indeterminate
                  memoryOracle := by rw [result.policy_exact]
                  context := result.context_exact, contextKind := result.contextKind_exact
                  cause := result.cause_exact, fetchContext := fetchContext
                  dataContext := (show descriptor.context = policy.context from rfl).trans
                    (policyContext.trans result.context_exact.symm)
                  space := rfl, ordering := rfl, ledgerEffect := rfl, authorityEffect := rfl }
              match h : selected.instruction with
              | .load32 displacement destination =>
                    .ok (.load selected.encoded
                    { displacement := displacement, destination := destination
                      instructionExact := h, fetch := fetch, fetchSpace := fetchSpace
                      encodingExact := selected.encoding_eq.symm, access := access
                      placed := ⟨plan.base, by
                        have eq : result.run.resolved.allocation = plan.allocation :=
                          Option.some.inj (result.run.resolved.allocationLookup.symm.trans plan.lookup)
                        rw [eq]; exact plan.placed⟩
                      intent := by simp [access, descriptor, purpose, h, AddressPlan.descriptor]
                      initialization := by simp [access, descriptor, purpose, h, AddressPlan.descriptor]
                      address := rfl
                      width := by
                        change selected.instruction.width = 4
                        simpa [Instruction.width] using congrArg Instruction.width h } rfl)
              | .store32Imm displacement immediate | .store64SignedImm32 displacement immediate =>
                  let payload := selected.instruction.payload?.getD []
                  let actual := access.writeData
                    (afterFetch.noteContext result.run.context result.run.contextKind) descriptor
                  .ok (.store selected.encoded
                      { fetch := fetch, fetchSpace := fetchSpace
                        encodingExact := selected.encoding_eq.symm, access := access
                        placed := ⟨plan.base, by
                          have eq : result.run.resolved.allocation = plan.allocation :=
                            Option.some.inj
                              (result.run.resolved.allocationLookup.symm.trans plan.lookup)
                          rw [eq]; exact plan.placed⟩
                        intent := by simp [access, descriptor, purpose, h, AddressPlan.descriptor]
                        initialization := by simp [access, descriptor, purpose, h, AddressPlan.descriptor]
                        producesInitialized := by simp [access, descriptor, purpose, h, AddressPlan.descriptor]
                        address := rfl
                        width := by rfl
                        payload := payload
                        payloadExact := by simp [payload, h, Instruction.payload?]
                        supplied := by rfl } rfl)

def fromFetched {policy : CpuAccessPolicy} {before : State}
    (fetched : FetchFactory.Success policy before) : Except Failure (Success fetched.dispatched.fetch) :=
  let metadata := fetched.observed.dispatch_metadata fetched.dispatched fetched.dispatch_exact
  fromSite policy fetched.dispatched.fetch
    (by
      rw [metadata.2.2.2.2, fetched.descriptor_exact]
      rfl)
    (by
      calc
        fetched.dispatched.fetch.descriptor.context = fetched.observed.descriptor.context :=
          congrArg AccessDescriptor.context metadata.2.2.2.2
        _ = policy.context := by rw [fetched.descriptor_exact]; rfl
        _ = fetched.observed.run.context := fetched.context_exact.symm
        _ = fetched.dispatched.fetch.run.context := metadata.2.1.symm)
    (by rw [metadata.2.1, fetched.context_exact])

theorem fetchedPolicy {policy : CpuAccessPolicy} {before : State}
    (fetched : FetchFactory.Success policy before) :
    fetched.dispatched.fetch.run.policy = FetchFactory.fetchPolicy policy := by
  have metadata := fetched.observed.dispatch_metadata fetched.dispatched fetched.dispatch_exact
  exact metadata.1.trans fetched.policy_exact

structure CompleteSuccess (policy : CpuAccessPolicy) (before : State) where
  fetched : FetchFactory.Success policy before
  execution : Success fetched.dispatched.fetch

def memoryMove (policy : CpuAccessPolicy) (before : State) :
    Except Failure (CompleteSuccess policy before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched =>
      match fromFetched fetched with
      | .error reason => .error reason
      | .ok success => .ok ⟨fetched, success⟩

end Grass.ISA.X86.Execution.MemoryMoveFactory
