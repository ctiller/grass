import Grass.Platform.Win32.LoadedDataAccess
import Grass.Platform.Win32.CpuVocabulary
import Grass.ISA.X86.Execution.AccessPolicy
import Grass.Op.ReadCompletion

/-!
# Fixed Windows x64 CPU operational policy

The policy is computed from checked loaded records and the instruction address.
There is no public operation-policy, oracle, fault-list or provenance override.
This is the operational side of the boundary; exact-policy/execution adequacy
is a separate obligation for the public certificate.

The base oracle reads initialized authoritative memory. It supplies no store
payload: instruction factories replace it with the actual operand-derived bytes.
The indeterminate fallback is unreachable for the fixed initialized-read demands;
it is not a permission to observe uninitialized bytes.
-/

namespace Grass.Platform.Win32.Cpu

open Grass.Core Grass.Memory Grass.Op Grass.ISA.X86
open Grass.Platform.Win32.Loader

/-- Fixed operational declarations, with no legacy proposition checklist. -/
def operationalProfile : OperationalProfile :=
  { id := ⟨"win32.x64.cpu"⟩, vocabularyVersion := 1, vocabulary := vocabulary }

/-- CPU operations use the actual memory oracle and all mandatory memory facets.
The generic memory authority checks remain active; no custom provider weakens them. -/
def operationPolicy : StepPolicy :=
  { profile := operationalProfile
    requiredFacets := [.memoryEffects, .faults, .restartability, .ordering]
    oracle := Oracle.ofMemory (fun _ _ => []) (fun _ _ _ => 0)
    authorities := []
    violationClassesDeclared := by
      intro class_ member
      exact transition_violation_declared class_ member
    vocabularyWellFormed := vocabulary_wellFormed }

/-- A successfully prepared read admitted by this exact operational policy has
an initialized resolved range, including for direct generic-step consumers. -/
theorem prepared_read_initialized {memory : MemoryState} {descriptor : AccessDescriptor}
    {space : AddressSpace} {resolved : memory.ResolvedAccess descriptor.provenance descriptor.range}
    (wellFormed : descriptor.WellFormedIn space)
    (admitted : operationPolicy.Admits descriptor) (reads : descriptor.intent.reads = true)
    (prepared : prepareAccess memory descriptor = .ok resolved) :
    resolved.RangeInitialized :=
  rangeInitialized_of_prepareAccess_allBytesInitialized prepared
    (admitted_read_initialized wellFormed admitted reads)

/-- `prepared_read_fallback_irrelevant` proves independence from the value chosen
as an indeterminate fallback for any such read. -/
theorem prepared_read_fallback_irrelevant {memory : MemoryState} {descriptor : AccessDescriptor}
    {space : AddressSpace} {resolved : memory.ResolvedAccess descriptor.provenance descriptor.range}
    (wellFormed : descriptor.WellFormedIn space)
    (admitted : operationPolicy.Admits descriptor) (reads : descriptor.intent.reads = true)
    (prepared : prepareAccess memory descriptor = .ok resolved)
    (left right : Nat → Grass.Std.Logical.Byte) :
    observedBytes resolved left = observedBytes resolved right :=
  observedBytes_eq_of_rangeInitialized resolved
    (prepared_read_initialized wellFormed admitted reads prepared) left right

/-- Event identity supplies distinguish repeated visits to this numeric site.
This label is derived from the executed address, never supplied independently. -/
def instructionCause (address : MachineAddress) : EventCause :=
  ⟨⟨"win32.x64.cpu@" ++ toString address.toNat⟩⟩

/-- Data provenance for the CPU's numeric read footprint, including a separate
IAT allocation. Exact import/API occurrence matching is a later handoff check. -/
def dataProvenance? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (address : MachineAddress) (width : Nat) :
    Option Provenance :=
  (loaded.dataRoot? address width).map DataRoot.provenance

/-- Construct the fixed CPU policy from actual loaded code and stack roots.
An absent executable logical region or stack lookup remains an explicit refusal.
The CPU factory rechecks these roots against its actual current machine. -/
def policy? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (before : Execution.State) :
    Option Execution.CpuAccessPolicy := do
  let code ← loaded.codeRoot? before.rip
  let stack ← loaded.stackProvenance?
  pure
    { operationPolicy := operationPolicy
      context := inputs.thread
      contextKind := .thread
      cause := instructionCause before.rip
      code := code.provenance
      stack := stack
      data := dataProvenance? loaded
      faults := fun _ => accessFaults }

/-- Success retains the exact computed roots, thread, cause, operational guards
and fault declaration. No field can be substituted at the construction seam. -/
theorem policy?_inputs {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : Execution.State}
    {policy : Execution.CpuAccessPolicy} (success : policy? loaded before = some policy) :
    ∃ code : CodeRoot loaded before.rip, ∃ stack,
      loaded.codeRoot? before.rip = some code ∧ loaded.stackProvenance? = some stack ∧
      policy.code = code.provenance ∧ policy.stack = stack ∧
      policy.context = inputs.thread ∧ policy.contextKind = .thread ∧
      policy.cause = instructionCause before.rip ∧
      policy.operationPolicy = operationPolicy ∧ policy.faults = (fun _ => accessFaults) ∧
      policy.data = dataProvenance? loaded := by
  unfold policy? at success
  obtain ⟨code, codeExact, rest⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨stack, stackExact, rest⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj rest
  exact ⟨code, stack, codeExact, stackExact, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Grass.Platform.Win32.Cpu
