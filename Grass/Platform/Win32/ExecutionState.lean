import Grass.ISA.X86.Execution.State
import Grass.Op.CallProtocol

/-!
# Windows execution carrier

This module combines one architectural x86 state with checked synchronous-call
bookkeeping.  It is deliberately only a carrier: no constructor or predicate
below establishes that a CALL, RET, provider transition, or terminal execution
has taken place.

The call-protocol state is stored as metadata plus the one canonical machine in
the x86 state.  `callProtocol?` repacks that metadata against that machine, so a
carrier never owns a second machine or recreates protocol state with `initial`.
-/

namespace Grass.Platform.Win32.ExecutionState

open Grass.Core Grass.Op

/-- The control position represented by the carrier.  `terminal` is an explicit
marker supplied by a later execution layer; it does not itself witness an exit
or any completed instruction sequence. -/
inductive Control where
  | caller (caller : ContextId)
  | pending (call : CallProtocol.CallId) (caller provider : ContextId)
  | terminal
deriving DecidableEq, Repr

/-- One x86 architectural state and all checked call-protocol metadata. -/
structure State (Request : Type) where
  /-- The sole machine representation in this carrier. -/
  machine : Grass.ISA.X86.Execution.State
  /-- All call-protocol data other than its machine. -/
  metadata : CallProtocol.Metadata Request
  control : Control
  /-- The metadata checks against the canonical machine. -/
  protocolValid : (metadata.pack? machine.machine).isSome

/-- Recheck the stored bookkeeping against the carrier's canonical machine. -/
def State.callProtocol? {Request : Type} (state : State Request) :
    Option (CallProtocol.State Request) :=
  state.metadata.pack? state.machine.machine

/-- Every carrier has a checked call-protocol projection. -/
theorem State.callProtocol?_isSome {Request : Type} (state : State Request) :
    state.callProtocol?.isSome :=
  state.protocolValid

/-- A pending control position must name live caller and provider contexts and
the exact pending protocol occurrence in a successful checked projection.  A
caller position names a live caller and has no pending occurrence for it.
`terminal` imposes no fabricated execution fact: a later receipt layer must
supply whatever evidence gives that marker operational meaning. -/
def State.ControlConsistent {Request : Type} (state : State Request) : Prop :=
  match state.control with
  | .caller caller =>
      ∃ protocol, state.callProtocol? = some protocol ∧
        (∃ kind, protocol.machine.contexts.lookup caller = some kind) ∧
        CallProtocol.callerPending protocol caller = false
  | .pending call caller provider =>
      ∃ protocol, state.callProtocol? = some protocol ∧
        (∃ kind, protocol.machine.contexts.lookup caller = some kind) ∧
        (∃ kind, protocol.machine.contexts.lookup provider = some kind) ∧
        ∃ record, protocol.pending.lookup call = some record ∧
          record.caller = caller ∧ record.agent = provider
  | .terminal => True

/-- Build a carrier from a checked call-protocol state and an x86 state that
contains that protocol state's machine.  The protocol metadata is retained
verbatim; no initial state is synthesized. -/
def State.ofCallProtocol {Request : Type} (protocol : CallProtocol.State Request)
    (machine : Grass.ISA.X86.Execution.State)
    (_sameMachine : machine.machine = protocol.machine) (control : Control) : State Request :=
  { machine := machine, metadata := protocol.metadata, control := control
    protocolValid := by
      rw [_sameMachine]
      simp [CallProtocol.State.metadata_pack?] }

/-- Successful checked projection exposes exactly the canonical machine and all
stored protocol metadata. -/
theorem State.callProtocol?_fields {Request : Type} {state : State Request}
    {protocol : CallProtocol.State Request}
    (success : state.callProtocol? = some protocol) :
    protocol.machine = state.machine.machine ∧ protocol.metadata = state.metadata :=
  CallProtocol.Metadata.pack?_fields success

@[simp] theorem State.ofCallProtocol_machine {Request : Type}
    (protocol : CallProtocol.State Request) (machine : Grass.ISA.X86.Execution.State)
    (sameMachine : machine.machine = protocol.machine) (control : Control) :
    (ofCallProtocol protocol machine sameMachine control).machine = machine := rfl

@[simp] theorem State.ofCallProtocol_metadata {Request : Type}
    (protocol : CallProtocol.State Request) (machine : Grass.ISA.X86.Execution.State)
    (sameMachine : machine.machine = protocol.machine) (control : Control) :
    (ofCallProtocol protocol machine sameMachine control).metadata = protocol.metadata := rfl

@[simp] theorem State.ofCallProtocol_control {Request : Type}
    (protocol : CallProtocol.State Request) (machine : Grass.ISA.X86.Execution.State)
    (sameMachine : machine.machine = protocol.machine) (control : Control) :
    (ofCallProtocol protocol machine sameMachine control).control = control := rfl

/-- Repacking a carrier built from a real protocol state recovers that complete
protocol state, including every metadata field and its checked proof fields. -/
theorem State.ofCallProtocol_callProtocol? {Request : Type}
    (protocol : CallProtocol.State Request) (machine : Grass.ISA.X86.Execution.State)
    (sameMachine : machine.machine = protocol.machine) (control : Control) :
    (ofCallProtocol protocol machine sameMachine control).callProtocol? = some protocol := by
  unfold callProtocol? ofCallProtocol
  dsimp
  rw [sameMachine]
  exact CallProtocol.State.metadata_pack? protocol

end Grass.Platform.Win32.ExecutionState
