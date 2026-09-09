import Grass.Platform.Win32.ApiRequest
import Grass.Platform.Win32.ExecutionState
import Grass.Platform.Win32.CallRuntime

/-!
# Raw Windows execution state

Raw execution retains the reached architectural machine even when protocol
metadata no longer checks against it. The checked execution carrier is a view,
not a restriction on the states that raw semantics can represent. Neither view
conversion nor a control marker establishes execution or terminal observation.
-/

namespace Grass.Platform.Win32.ExecutionState

/-- Exactly one CPU state, all original protocol metadata, control, and the
per-call runtime data needed to connect consecutive endpoint steps.
Validity is a reachable invariant, never a raw-state constructor premise. -/
structure RawState where
  machine : Grass.ISA.X86.Execution.State
  metadata : Grass.Op.CallProtocol.Metadata ApiRequest
  control : Control
  calls : CallRuntimeTable := .empty

/-- Preserve the checked carrier's machine, protocol metadata and control,
and attach the explicitly supplied runtime table. Empty is for initialization;
an ongoing call must pass its actual existing table. -/
def State.raw (state : State ApiRequest) (calls : CallRuntimeTable := .empty) : RawState :=
  ⟨state.machine, state.metadata, state.control, calls⟩

/-- The existing protocol check on this exact raw machine and metadata. -/
def RawState.ProtocolValid (raw : RawState) : Prop :=
  (raw.metadata.pack? raw.machine.machine).isSome

instance (raw : RawState) : Decidable raw.ProtocolValid :=
  inferInstanceAs (Decidable (raw.metadata.pack? raw.machine.machine).isSome)

/-- Obtain the existing checked machine/protocol/control view. Runtime data
stays with the original raw value and must be supplied when rebuilding it.
Failure also leaves the complete raw value available to its caller. -/
def RawState.checked? (raw : RawState) : Option (State ApiRequest) :=
  if valid : raw.ProtocolValid then
    some ⟨raw.machine, raw.metadata, raw.control, valid⟩
  else none

/-- A successful check plus the same retained table recovers this exact raw state. -/
theorem RawState.checked?_raw {raw : RawState} {checked : State ApiRequest}
    (success : raw.checked? = some checked) : checked.raw raw.calls = raw := by
  unfold checked? at success
  split at success
  · cases Option.some.inj success
    cases raw
    rfl
  · contradiction

/-- The original checked carrier round-trips, including its proof field. -/
@[simp] theorem State.raw_checked? (state : State ApiRequest) (calls : CallRuntimeTable := .empty) :
    (state.raw calls).checked? = some state := by
  unfold RawState.checked?
  rw [dif_pos (show (state.raw calls).ProtocolValid from state.protocolValid)]
  cases state
  rfl

/-- Check success has exactly the existing protocol-validity condition. -/
theorem RawState.checked?_isSome (raw : RawState) :
    raw.checked?.isSome ↔ raw.ProtocolValid := by
  unfold checked?
  split <;> simp_all

/-- Refusal exposes missing validity, not an absent raw state or execution. -/
theorem RawState.checked?_eq_none (raw : RawState) :
    raw.checked? = none ↔ ¬ raw.ProtocolValid := by
  unfold checked?
  split <;> simp_all

/-- Control consistency is a separate invariant of the exact checked view. -/
def RawState.ControlConsistent (raw : RawState) : Prop :=
  ∃ checked, raw.checked? = some checked ∧ checked.ControlConsistent

/-- Runtime data and protocol pending records have the same call domain and
endpoint kinds. This does not establish original-call or ABI/frame validity. -/
def RawState.RuntimeLinked (raw : RawState) : Prop :=
  (∀ entry ∈ raw.calls.entries, ∃ pending,
    raw.metadata.pending.lookup entry.1 = some pending ∧
      entry.2.MatchesRequest pending.request) ∧
  (∀ entry ∈ raw.metadata.pending.entries, ∃ runtime,
    raw.calls.lookup entry.1 = some runtime)

/-- A CPU outcome retains the original metadata and control even if repacking
will fail. This is a data operation, not a CPU-transition constructor. -/
def RawState.withMachine (raw : RawState)
    (machine : Grass.ISA.X86.Execution.State) : RawState :=
  { raw with machine := machine }

@[simp] theorem RawState.withMachine_machine (raw : RawState)
    (machine : Grass.ISA.X86.Execution.State) :
    (raw.withMachine machine).machine = machine := rfl

@[simp] theorem RawState.withMachine_metadata (raw : RawState)
    (machine : Grass.ISA.X86.Execution.State) :
    (raw.withMachine machine).metadata = raw.metadata := rfl

@[simp] theorem RawState.withMachine_control (raw : RawState)
    (machine : Grass.ISA.X86.Execution.State) :
    (raw.withMachine machine).control = raw.control := rfl

@[simp] theorem RawState.withMachine_calls (raw : RawState)
    (machine : Grass.ISA.X86.Execution.State) :
    (raw.withMachine machine).calls = raw.calls := rfl

/-- Update only the runtime entry at this identity. Actual issuance or service
must separately justify the update in the fixed endpoint relation. -/
def RawState.setCall (raw : RawState) (call : Grass.Op.CallProtocol.CallId)
    (runtime : CallRuntime) : RawState :=
  { raw with calls := raw.calls.insert call runtime }

/-- Remove only runtime data. This is not a protocol return or loan discharge. -/
def RawState.eraseCall (raw : RawState) (call : Grass.Op.CallProtocol.CallId) : RawState :=
  { raw with calls := raw.calls.erase call }

theorem RawState.setCall_lookup (raw : RawState) (call : Grass.Op.CallProtocol.CallId)
    (runtime : CallRuntime) : (raw.setCall call runtime).calls.lookup call = some runtime :=
  Grass.Std.Logical.FiniteMap.lookup_insert_self _ _ _

theorem RawState.setCall_other (raw : RawState) {call other : Grass.Op.CallProtocol.CallId}
    (different : other ≠ call) (runtime : CallRuntime) :
    (raw.setCall call runtime).calls.lookup other = raw.calls.lookup other :=
  Grass.Std.Logical.FiniteMap.lookup_insert_ne _ different _

theorem RawState.eraseCall_lookup (raw : RawState) (call : Grass.Op.CallProtocol.CallId) :
    (raw.eraseCall call).calls.lookup call = none :=
  Grass.Std.Logical.FiniteMap.lookup_erase_self _ _

theorem RawState.eraseCall_other (raw : RawState) {call other : Grass.Op.CallProtocol.CallId}
    (different : other ≠ call) :
    (raw.eraseCall call).calls.lookup other = raw.calls.lookup other :=
  Grass.Std.Logical.FiniteMap.lookup_erase_ne _ different

end Grass.Platform.Win32.ExecutionState
