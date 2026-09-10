import Grass.ISA.X86.Execution.MemoryMoveSelection
import Grass.ISA.X86.Execution.AccessPolicy
import Grass.ISA.X86.Execution.RunFactory
import Grass.ISA.X86.Execution.FetchFactory

namespace Grass.ISA.X86.Execution.MemoryMoveFactory

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86 MemoryMoveNormal

inductive Failure where
  | fetch (reason : FetchFactory.Failure)
  | unsupported (reached : State) (encoding : InsnEncoding)
  | missingData (reached : State) (address : MachineAddress)
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
  | storeRegister64 {instruction} (encoded : Instruction.Encoding instruction) {afterData}
      (receipt : StoreRegister64Normal instruction encoded before afterFetch afterData)
      (fetch_exact : receipt.fetch = fetch) : Success fetch
  | load64 {instruction} (encoded : Instruction.Encoding instruction) {afterData}
      (receipt : Load64Normal instruction encoded before afterFetch afterData)
      (fetch_exact : receipt.fetch = fetch) : Success fetch

namespace Success

def instruction {before : State} {afterFetch : MachineState} {fetch : FetchedSite before afterFetch} :
    Success fetch → MemoryMoveNormal.Instruction
  | @Success.store _ _ _ instruction _ _ _ _ => instruction
  | @Success.load _ _ _ instruction _ _ _ _ => instruction
  | @Success.storeRegister64 _ _ _ instruction _ _ _ _ => instruction
  | @Success.load64 _ _ _ instruction _ _ _ _ => instruction

/-- The provenance of the actual data access retained by either normal receipt. -/
def provenance {before : State} {afterFetch : MachineState} {fetch : FetchedSite before afterFetch} :
    Success fetch → Provenance
  | .store _ receipt _ => receipt.access.descriptor.provenance
  | .load _ receipt _ => receipt.access.descriptor.provenance
  | .storeRegister64 _ receipt _ => receipt.access.descriptor.provenance
  | .load64 _ receipt _ => receipt.access.descriptor.provenance

def result {before : State} {afterFetch : MachineState} {fetch : FetchedSite before afterFetch} :
    Success fetch → State
  | .store _ receipt _ => receipt.result
  | .load _ receipt _ => receipt.result
  | .storeRegister64 _ receipt _ => receipt.result
  | .load64 _ receipt _ => receipt.result

end Success

private def reached (before : State) {d : AccessDescriptor} :
    RunFactory.AccessFailure d → State
  | .rejected _ => before
  | .violations after | .preparationUnavailable after _ | .answerUnavailable after =>
      { before with machine := after }

def usesRspBase : MemOperand → Bool
  | .base .rsp _ | .baseIndex .rsp _ _ _ => true
  | _ => false

def selectedProvenance (policy : CpuAccessPolicy)
    (instruction : MemoryMoveNormal.Instruction)
    (address : MachineAddress) : Option Provenance :=
  match instruction with
  | .store32Imm _ _ | .store64SignedImm32 _ _ | .load32 _ _ => some policy.stack
  | .store64Reg operand _ | .load64 operand _ =>
      if usesRspBase operand then some policy.stack else policy.data address instruction.width

def selectedPurpose : MemoryMoveNormal.Instruction → AccessPurpose
  | .store32Imm _ _ | .store64SignedImm32 _ _ => .stackWrite
  | .load32 _ _ => .stackRead
  | .store64Reg operand _ => if usesRspBase operand then .stackWrite else .dataWrite
  | .load64 operand _ => if usesRspBase operand then .stackRead else .dataRead

private theorem store64Purpose (operand : MemOperand) (source : Gpr) :
    (match selectedPurpose (.store64Reg operand source) with
      | .dataWrite | .stackWrite => true | _ => false) = true := by
  cases operand <;> simp [selectedPurpose, usesRspBase] <;> split <;> simp_all

private theorem load64Purpose (operand : MemOperand) (destination : Gpr) :
    (match selectedPurpose (.load64 operand destination) with
      | .dataRead | .stackRead => true | _ => false) = true := by
  cases operand <;> simp [selectedPurpose, usesRspBase] <;> split <;> simp_all

/-- Internal leaf used by the fixed FetchFactory wrapper; all execution metadata is explicit. -/
private def fromSite (policy : CpuAccessPolicy) {before : State} {afterFetch : MachineState}
    (fetch : FetchedSite before afterFetch)
    (fetchSpace : fetch.descriptor.space = .cpuVirtual)
    (fetchContext : fetch.descriptor.context = fetch.run.context)
    (policyContext : policy.context = fetch.run.context) : Except Failure (Success fetch) :=
  match MemoryMoveSelection.select fetch.site.encoding with
  | none => .error (Failure.unsupported { before with machine := afterFetch } fetch.site.encoding)
  | some selected =>
      let address := Instruction.operandAddress before fetch.site.fallthroughRip
        selected.instruction.operand
      match selectedProvenance policy selected.instruction address with
      | none => .error (Failure.missingData { before with machine := afterFetch } address)
      | some provenance => match planAddress afterFetch.memory provenance address with
      | .error reason => .error (Failure.address { before with machine := afterFetch } reason)
      | .ok plan =>
          let purpose := selectedPurpose selected.instruction
          let descriptor := plan.descriptor policy purpose selected.instruction.width
          let writeData : MachineState → AccessDescriptor → Grass.Std.Logical.ByteSeq :=
            fun _ _ => match selected.instruction with
              | .store64Reg _ source => le64 (before.gpr source)
              | _ => selected.instruction.payload?.getD []
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
                      intent := by simp [access, descriptor, purpose, h, selectedPurpose, AddressPlan.descriptor]
                      initialization := by simp [access, descriptor, purpose, h, selectedPurpose, AddressPlan.descriptor]
                      address := by
                        change Address.numeric address = _
                        dsimp [address]
                        rw [h]
                        rfl
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
                        intent := by simp [access, descriptor, purpose, h, selectedPurpose, AddressPlan.descriptor]
                        initialization := by simp [access, descriptor, purpose, h, selectedPurpose, AddressPlan.descriptor]
                        producesInitialized := by simp [access, descriptor, purpose, h, selectedPurpose, AddressPlan.descriptor]
                        address := by
                          change Address.numeric address = _
                          dsimp [address]
                          rw [h]
                          rfl
                        width := by rfl
                        payload := payload
                        payloadExact := by simp [payload, h, Instruction.payload?]
                        supplied := by simp [access, writeData, h, payload] } rfl)
              | .store64Reg operand source =>
                  .ok (.storeRegister64 selected.encoded
                    { operand := operand, source := source, instructionExact := h
                      fetch := fetch, fetchSpace := fetchSpace
                      encodingExact := selected.encoding_eq.symm, access := access
                      placed := ⟨plan.base, by
                        have eq : result.run.resolved.allocation = plan.allocation :=
                          Option.some.inj
                            (result.run.resolved.allocationLookup.symm.trans plan.lookup)
                        rw [eq]; exact plan.placed⟩
                      intent := by
                        have hp := store64Purpose operand source
                        cases hpurpose : selectedPurpose (.store64Reg operand source) <;>
                          simp_all [access, descriptor, purpose, AddressPlan.descriptor]
                      initialization := by
                        have hp := store64Purpose operand source
                        cases hpurpose : selectedPurpose (.store64Reg operand source) <;>
                          simp_all [access, descriptor, purpose, AddressPlan.descriptor]
                      producesInitialized := by
                        have hp := store64Purpose operand source
                        cases hpurpose : selectedPurpose (.store64Reg operand source) <;>
                          simp_all [access, descriptor, purpose, AddressPlan.descriptor]
                      address := by
                        change Address.numeric address = _
                        dsimp [address]
                        rw [h]
                        simp [MemoryMoveNormal.Instruction.operand]
                      width := by
                        change selected.instruction.width = 8
                        simpa [MemoryMoveNormal.Instruction.width] using
                          congrArg MemoryMoveNormal.Instruction.width h
                      supplied := by simp [access, writeData, h] } rfl)
              | .load64 operand destination =>
                  .ok (.load64 selected.encoded
                    { operand := operand, destination := destination, instructionExact := h
                      fetch := fetch, fetchSpace := fetchSpace
                      encodingExact := selected.encoding_eq.symm, access := access
                      placed := ⟨plan.base, by
                        have eq : result.run.resolved.allocation = plan.allocation :=
                          Option.some.inj
                            (result.run.resolved.allocationLookup.symm.trans plan.lookup)
                        rw [eq]; exact plan.placed⟩
                      intent := by
                        have hp := load64Purpose operand destination
                        cases hpurpose : selectedPurpose (.load64 operand destination) <;>
                          simp_all [access, descriptor, purpose, AddressPlan.descriptor]
                      initialization := by
                        have hp := load64Purpose operand destination
                        cases hpurpose : selectedPurpose (.load64 operand destination) <;>
                          simp_all [access, descriptor, purpose, AddressPlan.descriptor]
                      address := by
                        change Address.numeric address = _
                        dsimp [address]
                        rw [h]
                        simp [MemoryMoveNormal.Instruction.operand]
                      width := by
                        change selected.instruction.width = 8
                        simpa [MemoryMoveNormal.Instruction.width] using
                          congrArg MemoryMoveNormal.Instruction.width h } rfl)

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

private theorem fromSite_selectedProvenance {policy : CpuAccessPolicy} {before : State}
    {afterFetch : MachineState} {fetch : FetchedSite before afterFetch}
    {fetchSpace : fetch.descriptor.space = .cpuVirtual}
    {fetchContext : fetch.descriptor.context = fetch.run.context}
    {policyContext : policy.context = fetch.run.context} {success : Success fetch}
    (ran : fromSite policy fetch fetchSpace fetchContext policyContext = .ok success) :
    selectedProvenance policy success.instruction
      (MemoryMoveNormal.Instruction.operandAddress before fetch.site.fallthroughRip
        success.instruction.operand) = some success.provenance := by
  unfold fromSite at ran
  split at ran
  · contradiction
  · rename_i selected selectionExact
    rcases selected with ⟨selectedInstruction, selectedEncoding, encodingExact⟩
    cases selectedInstruction <;> simp only at ran
    all_goals
      repeat first | split at ran | contradiction
    all_goals cases Except.ok.inj ran
    all_goals simp_all [selectedProvenance, AddressPlan.descriptor, Success.instruction,
      Success.provenance]

/-- Successful execution exposes the exact policy-selected provenance for the
decoded memory operand. This replaces the former family-wide stack equation. -/
theorem fromFetched_selectedProvenance {policy : CpuAccessPolicy} {before : State}
    {fetched : FetchFactory.Success policy before}
    {success : Success fetched.dispatched.fetch}
    (ran : fromFetched fetched = .ok success) :
    selectedProvenance policy success.instruction
      (MemoryMoveNormal.Instruction.operandAddress before
        fetched.dispatched.fetch.site.fallthroughRip success.instruction.operand) =
      some success.provenance := by
  unfold fromFetched at ran
  exact fromSite_selectedProvenance ran

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

/-- The legacy RSP-relative DWORD load keeps its exact stack provenance even
after the generic memory-operand families are added. -/
private theorem fromSite_load_stack {policy : CpuAccessPolicy} {before : State}
    {afterFetch : MachineState} {fetch : FetchedSite before afterFetch}
    {fetchSpace : fetch.descriptor.space = .cpuVirtual}
    {fetchContext : fetch.descriptor.context = fetch.run.context}
    {policyContext : policy.context = fetch.run.context}
    {instruction : MemoryMoveNormal.Instruction}
    {encoded : MemoryMoveNormal.Instruction.Encoding instruction}
    {afterData : MachineState}
    {receipt : LoadNormal instruction encoded before afterFetch afterData}
    {fetchExact : receipt.fetch = fetch}
    (ran : fromSite policy fetch fetchSpace fetchContext policyContext =
      .ok (.load encoded receipt fetchExact)) :
    receipt.access.descriptor.provenance = policy.stack := by
  unfold fromSite at ran
  split at ran
  · contradiction
  · rename_i selected selectionExact
    rcases selected with ⟨selectedInstruction, selectedEncoding, encodingExact⟩
    cases selectedInstruction <;> simp only at ran
    all_goals
      repeat first | split at ran | contradiction
    all_goals cases Except.ok.inj ran
    all_goals simp_all [selectedProvenance, AddressPlan.descriptor]

theorem memoryMove_load_stack {policy : CpuAccessPolicy} {before : State}
    {fetched : FetchFactory.Success policy before}
    {instruction : MemoryMoveNormal.Instruction}
    {encoded : MemoryMoveNormal.Instruction.Encoding instruction}
    {afterData : MachineState}
    {receipt : LoadNormal instruction encoded before fetched.after afterData}
    {fetchExact : receipt.fetch = fetched.dispatched.fetch}
    (ran : memoryMove policy before = .ok ⟨fetched, .load encoded receipt fetchExact⟩) :
    receipt.access.descriptor.provenance = policy.stack := by
  unfold memoryMove at ran
  split at ran
  · contradiction
  · split at ran
    · contradiction
    · rename_i execution executed
      cases Except.ok.inj ran
      unfold fromFetched at executed
      exact fromSite_load_stack executed

end Grass.ISA.X86.Execution.MemoryMoveFactory
