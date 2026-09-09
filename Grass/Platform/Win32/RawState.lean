import Grass.Platform.Win32.ApiRequest
import Grass.Platform.Win32.ExecutionState

/-!
# Raw Windows execution state

Raw execution retains the reached architectural machine even when protocol
metadata no longer checks against it. The checked execution carrier is a view,
not a restriction on the states that raw semantics can represent. Neither view
conversion nor a control marker establishes execution or terminal observation.
-/

namespace Grass.Platform.Win32.ExecutionState

/-- Exactly one CPU state, all original protocol metadata, and control data.
Validity is a reachable invariant, never a raw-state constructor premise. -/
structure RawState where
  machine : Grass.ISA.X86.Execution.State
  metadata : Grass.Op.CallProtocol.Metadata ApiRequest
  control : Control

/-- Forget only the proof that metadata checks; preserve every data field. -/
def State.raw (state : State ApiRequest) : RawState :=
  ⟨state.machine, state.metadata, state.control⟩

/-- The existing protocol check on this exact raw machine and metadata. -/
def RawState.ProtocolValid (raw : RawState) : Prop :=
  (raw.metadata.pack? raw.machine.machine).isSome

instance (raw : RawState) : Decidable raw.ProtocolValid :=
  inferInstanceAs (Decidable (raw.metadata.pack? raw.machine.machine).isSome)

/-- Obtain the existing checked view without changing any raw field.
Failure leaves the raw value available to its caller. -/
def RawState.checked? (raw : RawState) : Option (State ApiRequest) :=
  if valid : raw.ProtocolValid then
    some ⟨raw.machine, raw.metadata, raw.control, valid⟩
  else none

/-- A successful check recovers exactly this raw state. -/
theorem RawState.checked?_raw {raw : RawState} {checked : State ApiRequest}
    (success : raw.checked? = some checked) : checked.raw = raw := by
  unfold checked? at success
  split at success
  · cases Option.some.inj success
    cases raw
    rfl
  · contradiction

/-- The original checked carrier round-trips, including its proof field. -/
@[simp] theorem State.raw_checked? (state : State ApiRequest) :
    state.raw.checked? = some state := by
  unfold RawState.checked?
  rw [dif_pos (show state.raw.ProtocolValid from state.protocolValid)]
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

end Grass.Platform.Win32.ExecutionState
