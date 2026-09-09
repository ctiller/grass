import Grass.Std.Console.WriteAll
import Grass.Process.Sequential.Adapter

/-!
# Sequential consumer of the write-all kernel

This is a portable implementation model for Hello's byte-write loop, using the
existing `SequentialMachine` and its occurrence-preserving adapter. It is not
the precious text specification or a Win32 provider certificate. A failed
write's count describes externally emitted bytes, not a count the application
must be able to recover from the API.

The write result carries a ghost emitted-prefix witness. This machine is a
semantic reference consumer, not executable API-call code: provider refinement
must relate API-visible control decisions and physical output history to these
results. In particular, no lowering may read the failure witness as a runtime
byte count. Failure terminates regardless of the witness; its cursor records
the history for reasoning only.

An effect result is published by one internal step because the existing
sequential surface emits observations on internal decisions. A blocked effect
keeps its outstanding occurrence; pending is not a synthetic result that
consumes and reissues it. These local proofs do not yet provide the complete
infinite-pending semantics or responsive-strategy theorem required by Hello.
-/

namespace Grass.Std.Console.WriteProcess

open Grass.Process Grass.Specification Grass.Std.Logical

/-- The portable operations used by this model. -/
inductive Demand (payload : Vec Byte) where
  | stdout
  | write (cursor : WriteCursor payload)

/-- Semantic results at their exact demand, including a ghost emission witness. -/
def Demand.Result {payload : Vec Byte} : Demand payload → Type
  | .stdout => Bool
  | .write cursor => WriteResponse cursor

/-- Portable model boundary; provider obligations are added during projection. -/
@[reducible] def boundary (payload : Vec Byte) : DriverBoundary where
  ExternalEvent := Empty
  Demand := Demand payload
  Result := Demand.Result
  Observation := Vec Byte
  requirements := RequirementSet.empty

/-- Detailed completion cause, before the caller's outcome projection. -/
inductive Completion (payload : Vec Byte) where
  | unavailable
  | written (outcome : WriteOutcome) (cursor : WriteCursor payload)

/-- Control state contains a cursor, not a growing execution history. -/
inductive State (payload : Vec Byte) where
  | acquire
  | writing (cursor : WriteCursor payload)
  | publish (cursor : WriteCursor payload)
      (more : cursor.committed < payload.length) (response : WriteResponse cursor)
  | finished (outcome : WriteOutcome) (cursor : WriteCursor payload)
  | unavailable

/-- The initial cursor has committed no bytes. -/
def startCursor (payload : Vec Byte) : WriteCursor payload := ⟨0, Nat.zero_le _⟩

/-- Consume the kernel's exact continuation without choosing another policy. -/
def continueAt {payload : Vec Byte} : WriteNext payload → State payload
  | .retry cursor => .writing cursor
  | .done outcome cursor => .finished outcome cursor

/-- Success requires completion; no-progress requires an unfinished payload. -/
def OutcomeValid {payload : Vec Byte} (outcome : WriteOutcome)
    (cursor : WriteCursor payload) : Prop :=
  match outcome with
  | .success => cursor.committed = payload.length
  | .writeFailed => True
  | .noProgress => cursor.committed < payload.length

/-- State invariant consumed by `machine`. -/
def Valid {payload : Vec Byte} : State payload → Prop
  | .finished outcome cursor => OutcomeValid outcome cursor
  | _ => True

/-- `continueAt_valid` uses the kernel's success and no-progress laws. -/
theorem continueAt_valid {payload : Vec Byte} (cursor : WriteCursor payload)
    (more : cursor.committed < payload.length) (response : WriteResponse cursor) :
    Valid (continueAt (respond cursor more response)) := by
  generalize nextEq : respond cursor more response = next
  cases next with
  | retry next => trivial
  | done outcome next =>
    cases outcome with
    | success => exact respond_success_complete cursor more response next nextEq
    | writeFailed => trivial
    | noProgress => exact (respond_noProgress_unchanged cursor more response next nextEq).2

/-- Total decisions over every result admitted by the portable demand. -/
def decide {payload : Vec Byte} :
    State payload → SequentialDecision (boundary payload) (State payload) (Completion payload)
  | .acquire => .effect .stdout (fun available =>
      match available with
      | true => .writing (startCursor payload)
      | false => .unavailable)
  | .writing cursor =>
      if more : cursor.committed < payload.length then
        .effect (.write cursor) (fun response => .publish cursor more response)
      else .terminal (.written .success cursor)
  | .publish cursor more response =>
      .internal (continueAt (respond cursor more response)) [response.emitted]
  | .finished outcome cursor => .terminal (.written outcome cursor)
  | .unavailable => .terminal .unavailable

/-- At most one internal publication step separates effect frontiers. -/
def rank {payload : Vec Byte} : State payload → Nat
  | .publish _ _ _ => 1
  | _ => 0

/-- The write-all model uses the existing sequential authoring surface. -/
def machine (payload : Vec Byte) : SequentialMachine (boundary payload) where
  State := State payload
  Request := Unit
  Terminal := Completion payload
  initial := fun _ => .acquire
  decide := decide
  invariant := Valid
  initialInvariant := fun _ => trivial
  internalPreserves := by
    intro state next observations decision _
    cases state with
    | acquire => simp [decide] at decision
    | writing cursor => simp only [decide] at decision; split at decision <;> contradiction
    | publish cursor more response =>
      cases decision
      exact continueAt_valid cursor more response
    | finished outcome cursor => simp [decide] at decision
    | unavailable => simp [decide] at decision
  effectResumes := by
    intro state demand resume decision _ result
    cases state with
    | acquire =>
      cases decision
      cases result <;> trivial
    | writing cursor =>
      simp only [decide] at decision
      split at decision
      · cases decision; trivial
      · contradiction
    | publish cursor more response => simp [decide] at decision
    | finished outcome cursor => simp [decide] at decision
    | unavailable => simp [decide] at decision
  Rank := Nat
  rankLt := Nat.lt
  rankWellFounded := Nat.lt_wfRel.wf
  rank := rank
  internalDecreases := by
    intro state next observations decision
    cases state with
    | acquire => simp [decide] at decision
    | writing cursor => simp only [decide] at decision; split at decision <;> contradiction
    | publish cursor more response =>
      cases decision
      cases respond cursor more response <;> exact Nat.zero_lt_succ 0
    | finished outcome cursor => simp [decide] at decision
    | unavailable => simp [decide] at decision

/-- The adapter supplies exact occurrence accounting for this same machine. -/
def program (payload : Vec Byte) : DirectRelationalProgram (boundary payload) :=
  (machine payload).elaborate

/-- Recover the committed prefix represented by a model state. -/
def emittedPrefix {payload : Vec Byte} : State payload → Vec Byte
  | .acquire | .unavailable => Vec.empty
  | .writing cursor | .publish cursor _ _ | .finished _ cursor =>
      payload.take cursor.committed

/-- Concatenate a process observation segment using the logical byte API. -/
def bytesOf : List (Vec Byte) → Vec Byte
  | [] => Vec.empty
  | chunk :: rest => chunk ++ bytesOf rest

/-- Every internal publication extends the recorded prefix by exactly its bytes. -/
theorem internal_bytes {payload : Vec Byte} (state next : State payload)
    (observations : List (Vec Byte))
    (decision : decide state = .internal next observations) :
    emittedPrefix next = emittedPrefix state ++ bytesOf observations := by
  cases state with
  | acquire => simp [decide] at decision
  | writing cursor => simp only [decide] at decision; split at decision <;> contradiction
  | publish cursor more response =>
    cases decision
    have conservation := respond_prefix_exact cursor more response
    cases resultEq : respond cursor more response <;>
      simpa [resultEq, continueAt, emittedPrefix, WriteNext.cursor, bytesOf] using conservation
  | finished outcome cursor => simp [decide] at decision
  | unavailable => simp [decide] at decision

/-- Receiving a result records no bytes until its internal publication step. -/
theorem effect_bytes {payload : Vec Byte} (state : State payload)
    (demand : Demand payload) (resume : Demand.Result demand → State payload)
    (decision : decide state = .effect demand resume) (result : Demand.Result demand) :
    emittedPrefix (resume result) = emittedPrefix state := by
  cases state with
  | acquire =>
    cases decision
    cases result <;> simp [emittedPrefix, startCursor]
  | writing cursor =>
    simp only [decide] at decision
    split at decision
    · cases decision; rfl
    · contradiction
  | publish cursor more response => simp [decide] at decision
  | finished outcome cursor => simp [decide] at decision
  | unavailable => simp [decide] at decision

/-- `step_accounting` preserves the invariant and accounts for every adapter-step byte. -/
theorem step_accounting {payload : Vec Byte}
    (before after : (machine payload).Point) (event : (machine payload).Event)
    (issued : Bag (machine payload).Occurrence) (observations : List (Vec Byte))
    (valid : Valid before.state)
    (step : (program payload).Step before event after issued observations) :
    Valid after.state ∧
      emittedPrefix after.state = emittedPrefix before.state ++ bytesOf observations := by
  obtain ⟨_, _, transition⟩ := step
  cases event with
  | internal =>
    exact ⟨(machine payload).internalPreserves _ _ _ transition valid,
      internal_bytes before.state after.state observations transition⟩
  | result occurrence answer =>
    obtain ⟨held, resumed, rfl⟩ := transition
    have present : occurrence ∈ (machine payload).held before := by
      rw [held]; simp
    have decision := (machine payload).held_issues present
    have pointEq := (machine payload).held_point present
    change (machine payload).decide occurrence.point.state =
      .effect occurrence.demand occurrence.resume at decision
    rw [pointEq] at decision
    rw [resumed]
    refine ⟨(machine payload).effectResumes _ _ _ decision valid answer, ?_⟩
    simpa [bytesOf] using
      effect_bytes before.state occurrence.demand occurrence.resume decision answer

/-- A written terminal decision exposes the cursor represented by its state. -/
theorem terminal_prefix {payload : Vec Byte} (state : State payload)
    (outcome : WriteOutcome) (cursor : WriteCursor payload)
    (terminal : decide state = .terminal (.written outcome cursor)) :
    emittedPrefix state = payload.take cursor.committed := by
  cases state with
  | acquire => simp [decide] at terminal
  | writing before =>
    simp only [decide] at terminal
    split at terminal
    · contradiction
    · cases terminal; rfl
  | publish before more response => simp [decide] at terminal
  | finished result before => cases terminal; rfl
  | unavailable => simp [decide] at terminal

/-- Every state's recorded output is a bounded prefix of its payload. -/
theorem state_prefix {payload : Vec Byte} (state : State payload) :
    ∃ count, count ≤ payload.length ∧ emittedPrefix state = payload.take count := by
  cases state with
  | acquire | unavailable => exact ⟨0, Nat.zero_le _, (Vec.take_zero payload).symm⟩
  | writing cursor | publish cursor _ _ | finished _ cursor =>
    exact ⟨cursor.committed, cursor.within, rfl⟩

/-- A successful terminal decision denotes the entire payload. -/
theorem terminal_success {payload : Vec Byte} (state : State payload)
    (cursor : WriteCursor payload) (valid : Valid state)
    (terminal : decide state = .terminal (.written .success cursor)) :
    cursor.committed = payload.length := by
  cases state with
  | acquire => simp [decide] at terminal
  | writing before =>
    simp only [decide] at terminal
    split at terminal
    · contradiction
    · cases terminal; have := cursor.within; omega
  | publish before more response => simp [decide] at terminal
  | finished outcome before => cases terminal; exact valid
  | unavailable => simp [decide] at terminal

/-- No-progress termination denotes a proper prefix, not success in disguise. -/
theorem terminal_noProgress {payload : Vec Byte} (state : State payload)
    (cursor : WriteCursor payload) (valid : Valid state)
    (terminal : decide state = .terminal (.written .noProgress cursor)) :
    cursor.committed < payload.length := by
  cases state with
  | acquire => simp [decide] at terminal
  | writing before => simp only [decide] at terminal; split at terminal <;> cases terminal
  | publish before more response => simp [decide] at terminal
  | finished outcome before => cases terminal; exact valid
  | unavailable => simp [decide] at terminal

/-- Unavailable stdout finishes without publishing bytes. -/
theorem terminal_unavailable {payload : Vec Byte} (state : State payload)
    (terminal : decide state = .terminal .unavailable) : emittedPrefix state = Vec.empty := by
  cases state with
  | acquire => simp [decide] at terminal
  | writing before => simp only [decide] at terminal; split at terminal <;> cases terminal
  | publish before more response => simp [decide] at terminal
  | finished outcome before => simp [decide] at terminal
  | unavailable => rfl

end Grass.Std.Console.WriteProcess
