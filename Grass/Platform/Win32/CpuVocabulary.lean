import Grass.Memory.Profile

/-!
# Fixed vocabulary for the Windows x64 CPU access boundary

This is operational vocabulary, not an adequacy package. In particular, naming
the represented access faults does not prove that all physical exceptions,
interruptions or aborts have been covered. The instruction outcome relation and
Windows delivery correspondence must retain those alternatives separately.
-/

namespace Grass.Platform.Win32.Cpu

open Grass.Core Grass.Memory

/-- `accessFaults` lists the represented architectural access-fault classes.
Instruction-specific
applicability and priority are proved by the x86 owner. -/
def accessFaults : List FaultClassId :=
  [.pageFault, .generalProtection, .alignmentCheck, .stackFault]

/-- Fixed names admitted by the current CPU/image/stack and API-loan boundary.
Empty profile-specific ordering and justification registries authorize no
invented initialization, atomicity or visibility rules. -/
def vocabulary : AdmittedVocabulary :=
  { addressSpaces := .cpuOnly
    faultClasses := ⟨accessFaults⟩
    allocationSources := ⟨[.stack, .imageMapping]⟩
    provenanceStepKinds := ⟨[.frame, .slot, .imageSection, .symbol]⟩
    auditViolationClasses := ⟨AuditViolationClass.emittedByTransition⟩
    obligationKinds := ⟨[]⟩
    grantKinds := ⟨[.loan, .frame]⟩
    protocols := ⟨[]⟩
    orderingModes := ⟨[]⟩
    orderingScopes := ⟨[]⟩
    contextKinds := ⟨[.thread, .externalAgent, .loader, .interruptHandler]⟩
    initializationJustifications := ⟨[]⟩
    atomicityJustifications := ⟨[]⟩
    faultVisibilityRules := ⟨[]⟩ }

/-- The fixed vocabulary does not conflate incompatible justification names. -/
theorem vocabulary_wellFormed : vocabulary.WellFormed := by decide

/-- Every violation the generic transition can emit remains representable. -/
theorem transition_violation_declared (class_ : AuditViolationClass)
    (emitted : class_ ∈ AuditViolationClass.emittedByTransition) :
    vocabulary.auditViolationClasses.Recognizes class_ := emitted

/-- Every declared access-fault alternative is admitted by the fixed registry. -/
theorem access_fault_declared (fault : FaultClassId) (member : fault ∈ accessFaults) :
    vocabulary.faultClasses.Recognizes fault := member

/-- `admitted_read_initialized` proves that direct generic-step clients must
demand initialization: the fixed registry has no initialization exception and
`AccessDescriptor.WellFormedIn` excludes a reading intent with `readsNothing`. -/
theorem admitted_read_initialized {descriptor : AccessDescriptor} {space : AddressSpace}
    (wellFormed : descriptor.WellFormedIn space)
    (admitted : vocabulary.Admits descriptor) (reads : descriptor.intent.reads = true) :
    descriptor.initialization = .allBytesInitialized := by
  cases initialization : descriptor.initialization with
  | allBytesInitialized => rfl
  | permitsUninitialized justification =>
      have forbidden := AdmittedVocabulary.not_admits_of_unregistered_justification
        (vocabulary := vocabulary) (d := descriptor) (justification := justification)
        (by simp [initialization]) (by simp [vocabulary, NameRegistry.Recognizes])
      exact False.elim (forbidden admitted)
  | readsNothing =>
      exact False.elim ((wellFormed.initializationMatchesIntent.mp reads) initialization)

end Grass.Platform.Win32.Cpu
