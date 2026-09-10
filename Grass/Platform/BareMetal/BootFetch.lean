import Grass.Platform.BareMetal.BootMemory
import Grass.Op.AccessFactory
import Grass.Op.ReadObservation

/-!
# Physical boot-code observations

An admitted entry is read by the shared singleton-access factory. The descriptor
and memory oracle are fixed here; a successful result retains the actual step,
backing observation and event. This is a no-fault model execution. Hardware fault
exclusion and firmware provenance remain external applicability requirements.
-/

namespace Grass.Platform.BareMetal.BootFetch

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical BootMemory

/-- The ordinary RAM space required by this bounded physical entry reader. -/
def ramSpace : AddressSpace :=
  { id := .cpuPhysical, repr := .numeric 64, memoryType := .writeBack
    coherence := .hostCoherent }

/-- Operational inputs with the exact physical RAM declaration. Hardware fault
completeness and the processor's translation regime remain applicability duties. -/
structure Policy where
  operation : StepPolicy
  ramDeclared : operation.profile.vocabulary.addressSpaces.find? .cpuPhysical = some ramSpace
  faults : List FaultClassId
  cause : EventCause

/-- `memoryPolicy` obtains every observed byte from the resolved shared backing. -/
def memoryPolicy (policy : Policy) : StepPolicy :=
  { policy.operation with oracle := Oracle.ofMemory (fun _ _ => []) (fun _ _ _ => 0) }

variable {map : PhysicalMap} {context : ContextId} {before : MachineState}
  {admission : Admission map context before} {id : AllocId} {range : ByteRange}

/-- `descriptor` derives PC, provenance and extent from the checked entry. -/
def descriptor (policy : Policy) (entry : Entry admission id range) : AccessDescriptor :=
  { context := context, address := .numeric entry.pc, space := .cpuPhysical
    provenance := entry.provenance, range := range, intent := .execute
    requiredPermission := .readExecute, alignment := 1
    initialization := .allBytesInitialized, producesInitialized := false
    ordering := .plain, admittedFaults := policy.faults, restartability := .restartable
    ledgerEffect := [], authorityEffect := [] }

/-- A success is the shared factory's actual singleton execution receipt. -/
abbrev Success (policy : Policy) (entry : Entry admission id range) :=
  AccessFactory.AccessSuccess (memoryPolicy policy) admission.machine
    (descriptor policy entry) context .thread policy.cause

/-- `fetch` executes the fixed physical read and preserves the factory's failures. -/
def fetch (policy : Policy) (entry : Entry admission id range) :
    Except (AccessFactory.AccessFailure (descriptor policy entry)) (Success policy entry) :=
  AccessFactory.access (memoryPolicy policy) admission.machine (descriptor policy entry)
    context .thread policy.cause

namespace Success

variable {policy : Policy} {entry : Entry admission id range}

/-- The byte sequence extracted from the actual completed read. -/
def bytes (success : Success policy entry) : ByteSeq :=
  AccessFactory.AccessRun.readBytes success.run rfl

/-- `observed_exact` identifies the bytes actually returned by the committed read. -/
theorem observed_exact (success : Success policy entry) :
    success.run.complete.committed.observed = some success.bytes :=
  AccessFactory.AccessRun.readBytes_exact success.run rfl

/-- `observed_backing` derives the shared observation from this run's selected memory oracle. -/
theorem observed_backing (success : Success policy entry) :
    success.bytes = observedBytes success.run.resolved (fun _ => 0) :=
  AccessFactory.AccessRun.readBytes_backing success.run (fun _ _ => []) (fun _ _ _ => 0)
    (by rw [success.policy_exact]; rfl) rfl

/-- `bytes_length` ties the actual observation to the selected entry extent. -/
theorem bytes_length (success : Success policy entry) : success.bytes.length = range.size :=
  AccessFactory.AccessRun.readBytes_length success.run rfl

/-- `storage_frame` derives preservation from the actual neutral execute read. -/
theorem storage_frame (success : Success policy entry) :
    success.after.memory = before.memory ∧
      success.after.obligations = admission.machine.obligations := by
  rw [success.run.prepared_result]
  exact performPreparedAccess_readOnly_noEffects_frame success.run.policy
    (admission.machine.noteContext success.run.context success.run.contextKind)
    (descriptor policy entry) success.run.resolved success.run.prepared
    (.completed success.run.complete) success.run.contextKind success.run.cause rfl rfl rfl

/-- `placed` connects the executed resolution to the admitted allocation base. -/
theorem placed (success : Success policy entry) :
    success.run.resolved.allocation.base = some entry.base := by
  have recordEq : success.run.resolved.allocation = entry.record :=
    Option.some.inj (success.run.resolved.allocationLookup.symm.trans entry.lookup)
  rw [recordEq]
  exact entry.baseExact

end Success
end Grass.Platform.BareMetal.BootFetch
