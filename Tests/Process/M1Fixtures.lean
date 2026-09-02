import Grass.Process.Correct
import Grass.Process.Protocol.Registry

/-!
# M1 fixtures for the process author vocabulary

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §3.3 lists the cases this milestone exits
on. Each is a theorem: `docs/FOUNDATION.md` law 3 forbids an executed example
standing in for a proof, so nothing here is an `#eval`.

The point of a fixture corpus at this layer is not coverage of the definitions.
It is that a reviewer can read one small process and check that the linearity
claims in `Grass/Process/Run.lean` are true of a thing that actually exists —
in particular the two negative fixtures, which show that a bad claim is not
merely unproved but unconstructible.
-/

namespace Grass.Process.Tests

open Grass.Process

/-! ## A small process

`Countdown` starts at its request, issues that many `tick` demands, and
decrements once per settled demand. A `log` demand answers with a `Bool` and
issues a fresh `tick`, which is what gives the fixtures a transition that
consumes one occurrence and issues another.
-/

/-- The demands. `log`'s result is a `Bool`; `tick`'s is not, which is the point
of the dependent result schema. -/
inductive Demand
  | tick
  | log
  deriving DecidableEq, Repr

/-- The dependent result schema. -/
@[reducible] def Result : Demand → Type
  | .tick => Unit
  | .log => Bool

/-- What the specification may observe. -/
inductive Observation
  | beep
  deriving DecidableEq, Repr

/-- Entropy from outside. -/
inductive ExternalEvent
  | wake
  deriving DecidableEq, Repr

/-- Why an outstanding demand was abandoned. -/
inductive Interrupt
  | abandoned
  deriving DecidableEq, Repr

/-- The vocabulary. Faults and environment violations are excluded by
construction; interruptions are not, because a fixture needs one. -/
@[reducible] def vocabulary : ProcessVocabulary.{0} where
  ExternalEvent := ExternalEvent
  Demand := Demand
  Result := Result
  Observation := Observation
  InterruptReason := Interrupt
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

/-- The countdown process. -/
@[reducible] def countdown : ProcessSpec.{0, 0} where
  toProcessVocabulary := vocabulary
  Request := Nat
  State := Nat
  TerminalResult := Unit
  Initial := fun request state issued emitted =>
    state = request ∧ issued = Bag.ofList (List.replicate request Demand.tick) ∧
      emitted = []
  Terminal := fun _ state _ => state = 0
  Step := fun state event after issued emitted =>
    match event with
    | .external .wake => after = state ∧ issued = 0 ∧ emitted = []
    | .result .tick _ => after = state - 1 ∧ issued = 0 ∧ emitted = [Observation.beep]
    | .result .log _ =>
        after = state ∧ issued = Bag.ofList [Demand.tick] ∧ emitted = []
    | .interrupted _ _ => after = state - 1 ∧ issued = 0 ∧ emitted = []
    | .fault fault => fault.elim
    | .environmentViolation violation => violation.elim
  TerminalDisposition := fun _ _ _ demand disposition =>
    demand = Demand.tick ∧ disposition = .permittedPending
  view := none

/-! ## Fixture 1 — a silent step

An external event that issues nothing and emits nothing is an ordinary
stuttering transition. It changes neither the outstanding bag nor the trace.
-/

theorem silent_step (state : Nat) (outstanding : Bag Demand)
    (observations : Trace Observation) :
    ProcessRunTransition countdown 3
      (.running state outstanding observations)
      (.running state (outstanding + 0) (observations ++ [])) :=
  ProcessRunTransition.stepExternal (event := ExternalEvent.wake) ⟨rfl, rfl, rfl⟩

theorem silent_step_changes_nothing (outstanding : Bag Demand)
    (observations : Trace Observation) :
    outstanding + 0 = outstanding ∧ observations ++ [] = observations := by
  simp

/-! ## Fixture 2 — equal values, distinct multiplicity

Two outstanding `tick` demands are two, not one, and settling one leaves one.
This is the fact a `Set` would lose.
-/

theorem two_ticks_is_not_one :
    Bag.ofList [Demand.tick, Demand.tick] ≠ Bag.ofList [Demand.tick] := by
  intro equal
  exact absurd (congrArg Bag.card equal) (by decide)

theorem two_ticks_card : (Bag.ofList [Demand.tick, Demand.tick]).card = 2 := rfl

theorem settling_one_tick_leaves_one :
    Bag.ConsumeExactlyOneMatching
      (Bag.ofList [Demand.tick, Demand.tick]) Demand.tick
      (Bag.ofList [Demand.tick]) := rfl

/--
Settling one of two identical demands is a transition, and the successor still
holds the other one. No single result discharged both.
-/
theorem settle_one_of_two (observations : Trace Observation) :
    ProcessRunTransition countdown 2
      (.running 2 (Bag.ofList [Demand.tick, Demand.tick]) observations)
      (.running 1 (Bag.ofList [Demand.tick] + 0)
        (observations ++ [Observation.beep])) :=
  ProcessRunTransition.stepResult (result := ())
    settling_one_tick_leaves_one ⟨rfl, rfl, rfl⟩

theorem settle_one_of_two_leaves_one :
    (Bag.ofList [Demand.tick] + (0 : Bag Demand)).card = 1 := by simp

/-! ## Fixture 3 — consume one, issue one

A `log` result consumes its own occurrence and issues a fresh `tick`. The
outstanding count is unchanged, but the bag is not: the settled occurrence is
gone and a different one is live.
-/

theorem result_consumes_one_issues_one (observations : Trace Observation) :
    ProcessRunTransition countdown 1
      (.running 1 (Bag.ofList [Demand.log]) observations)
      (.running 1 (0 + Bag.ofList [Demand.tick]) (observations ++ [])) :=
  ProcessRunTransition.stepResult (result := true) rfl ⟨rfl, rfl, rfl⟩

theorem result_consumes_one_issues_one_exchanges :
    (0 + Bag.ofList [Demand.tick]) ≠ Bag.ofList [Demand.log] := by
  intro equal
  have member : Demand.log ∈ (0 + Bag.ofList [Demand.tick]) := by
    rw [equal]; simp
  simp at member

/-! ## Fixture 4 — an interruption consumes without a result

`docs/PROCESS.md` §2 makes interruption a settling event: it removes the
occurrence, and there is no `Result` value anywhere in the transition.
-/

theorem interruption_consumes_without_result (observations : Trace Observation) :
    ProcessRunTransition countdown 2
      (.running 2 (Bag.ofList [Demand.tick, Demand.tick]) observations)
      (.running 1 (Bag.ofList [Demand.tick] + 0) (observations ++ [])) :=
  ProcessRunTransition.stepInterrupted (reason := Interrupt.abandoned)
    settling_one_tick_leaves_one ⟨rfl, rfl, rfl⟩

/-! ## Fixture 5 — terminating with a nonempty remainder

`countdown` permits exactly one disposition: a `tick` may be left pending. So a
run holding ticks can terminate, and a run holding a `log` cannot.
-/

/-- The classification a terminating countdown supplies: everything pending. -/
def pendingTicks (request state : Nat) (ticks : Bag Demand)
    (onlyTicks : ∀ demand ∈ ticks, demand = Demand.tick) :
    TerminalDemandClassification countdown request state () ticks where
  resolved := 0
  transferred := 0
  pending := ticks
  partition := by simp
  resolvedPermitted := by simp
  transferredPermitted := by simp
  pendingPermitted := fun demand member => ⟨onlyTicks demand member, rfl⟩

theorem terminate_with_pending_ticks (observations : Trace Observation) :
    ProcessRunTransition countdown 2
      (.running 0 (Bag.ofList [Demand.tick, Demand.tick]) observations)
      (.terminal 0 () observations) :=
  .terminate rfl
    (pendingTicks 2 0 _ (by intro demand member; simp at member; omega))

/--
**Negative fixture.** A run still holding a `log` demand cannot terminate: the
specification permits no disposition for it, so no classification exists.

This is `docs/FOUNDATION.md` law 7 being enforced rather than merely stated. The
obstruction is not that a proof is missing; it is that the terminal transition
has no inhabitant.
-/
theorem cannot_terminate_holding_log (request state : Nat) :
    ¬ Nonempty (TerminalDemandClassification countdown request state ()
      (Bag.ofList [Demand.log])) := by
  rintro ⟨classification⟩
  obtain ⟨disposition, isTick, _⟩ :=
    classification.covered (demand := Demand.log) (by simp)
  exact absurd isTick (by decide)

/--
**Negative fixture.** The partition, not a predicate on values, is what stops
one claim from discharging many occurrences: a classification of a two-tick bag
still has two ticks in its parts.
-/
theorem classification_conserves_multiplicity
    (classification : TerminalDemandClassification countdown 2 0 ()
      (Bag.ofList [Demand.tick, Demand.tick])) :
    classification.resolved.card + classification.transferred.card +
      classification.pending.card = 2 :=
  (classification.card_partition).symm

/-! ## Fixture 6 — a zero-transition terminal run

Request `0` starts at state `0` with nothing outstanding, which is already
terminal. `docs/PROCESS.md` §2 requires this to be an *initial terminal* state
rather than a running state followed by a hidden transition.
-/

theorem zero_request_is_initially_terminal :
    ProcessRunInitial countdown 0 (.terminal 0 () []) :=
  .terminal (issued := 0) ⟨rfl, rfl, rfl⟩ rfl
    (TerminalDemandClassification.empty countdown 0 0 ())

theorem zero_request_terminal_is_reachable :
    Reachable countdown 0 (.terminal 0 () []) :=
  .initial zero_request_is_initially_terminal

theorem zero_request_terminal_does_not_step
    {after : ProcessRunState countdown 0} :
    ¬ ProcessRunTransition countdown 0 (.terminal 0 () []) after :=
  ProcessRunTransition.not_from_terminal

/-! ## Fixture 7 — a deterministic process and its relational image -/

/-- A deterministic echo: every event returns to the same state, silently. -/
@[reducible] def echo : DeterministicProcess.{0, 0} vocabulary where
  Request := Unit
  State := Unit
  TerminalResult := Unit
  initial := fun _ => ((), 0, [])
  terminal := fun _ _ => some ()
  update := fun _ _ => ((), 0, [])
  terminalDisposition := fun _ _ _ _ _ => True
  view := none

theorem echo_step_is_functional {state : Unit} {event : ProcessEvent vocabulary}
    {afterLeft afterRight : Unit} {issuedLeft issuedRight : Bag Demand}
    {emittedLeft emittedRight : ObservationSegment Observation}
    (left : echo.toProcessSpec.Step state event afterLeft issuedLeft emittedLeft)
    (right : echo.toProcessSpec.Step state event afterRight issuedRight emittedRight) :
    afterLeft = afterRight ∧ issuedLeft = issuedRight ∧ emittedLeft = emittedRight :=
  echo.step_functional left right

theorem echo_initial_is_functional {request : Unit}
    {stateLeft stateRight : Unit} {issuedLeft issuedRight : Bag Demand}
    {emittedLeft emittedRight : ObservationSegment Observation}
    (left : echo.toProcessSpec.Initial request stateLeft issuedLeft emittedLeft)
    (right : echo.toProcessSpec.Initial request stateRight issuedRight emittedRight) :
    stateLeft = stateRight ∧ issuedLeft = issuedRight ∧ emittedLeft = emittedRight :=
  echo.initial_functional left right

/-! ## Fixture 8 — a protocol whose state is another protocol's runs

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.2 splits `ProcessSpec`'s universes so
that a protocol built *from* other protocols — which is what `flatten` produces
— keeps their interface types where they were and moves only its own private
state up. This fixture is the miniature of that: `observer`'s state is the run
state of `countdown`, which lives one universe up, while both processes share a
vocabulary at universe `0` and therefore fit in one registry.

Without the split, `observer` would sit above `countdown` entirely and could not
be registered beside it.
-/

/-- A process whose private state is a `countdown` run state. -/
@[reducible] def observer : ProcessSpec.{0, 1} where
  toProcessVocabulary := vocabulary
  Request := ULift Nat
  State := ULift (ProcessRunState countdown 2)
  TerminalResult := ULift Unit
  Initial := fun _ state issued emitted =>
    state = .up (.running 2 (Bag.ofList [Demand.tick, Demand.tick]) []) ∧
      issued = 0 ∧ emitted = []
  Terminal := fun _ state _ => ∃ result observations,
    state = .up (.terminal 0 result observations)
  Step := fun state _ after issued emitted =>
    after = state ∧ issued = 0 ∧ emitted = []
  TerminalDisposition := fun _ _ _ _ _ => False
  view := none

/-- `countdown` lifted to the same universes as `observer`, so both can be
registered. Only the private types move; the vocabulary is shared. -/
@[reducible] def countdownLifted : ProcessSpec.{0, 1} where
  toProcessVocabulary := vocabulary
  Request := ULift Nat
  State := ULift Nat
  TerminalResult := ULift Unit
  Initial := fun request state issued emitted =>
    countdown.Initial request.down state.down issued emitted
  Terminal := fun request state result =>
    countdown.Terminal request.down state.down result.down
  Step := fun state event after issued emitted =>
    countdown.Step state.down event after.down issued emitted
  TerminalDisposition := fun request state result demand disposition =>
    countdown.TerminalDisposition request.down state.down result.down demand
      disposition
  view := none

/-- The scope the base fragment owns. -/
@[reducible] def baseScope : ScopeId := ⟨["Tests", "Process", "Countdown"]⟩

/-- The scope the extension owns. -/
@[reducible] def observerScope : ScopeId := ⟨["Tests", "Process", "Observer"]⟩

/-- The registry a subsystem starts with. -/
@[reducible] def baseRegistry : ProtocolRegistry.{0, 1, 0} :=
  (⟨baseScope, Unit, fun _ => countdownLifted⟩ :
    RegistryFragment.{0, 1, 0}).toRegistry

/-- The registry it is extended with. -/
@[reducible] def observerRegistry : ProtocolRegistry.{0, 1, 0} :=
  (⟨observerScope, Unit, fun _ => observer⟩ :
    RegistryFragment.{0, 1, 0}).toRegistry

theorem scopes_disjoint :
    ProtocolRegistry.ScopesDisjoint baseRegistry observerRegistry := by
  intro _ _
  show baseScope ≠ observerScope
  decide

/-- The extension. -/
@[reducible] def extendedRegistry : ProtocolRegistry.{0, 1, 0} :=
  ProtocolRegistry.merge baseRegistry observerRegistry scopes_disjoint

/-- Every prior key keeps its protocol and its scope in the extension. -/
def baseEmbeds : RegistryEmbedding baseRegistry extendedRegistry :=
  ProtocolRegistry.mergeLeft baseRegistry observerRegistry scopes_disjoint

theorem base_protocol_preserved (key : baseRegistry.Key) :
    extendedRegistry.protocol (baseEmbeds.embed key) =
      baseRegistry.protocol key :=
  baseEmbeds.protocolExact key

theorem base_scope_preserved (key : baseRegistry.Key) :
    extendedRegistry.scope (baseEmbeds.embed key) = baseScope :=
  baseEmbeds.scopeExact key

/-- The new protocol is present and is exactly the one that was registered. -/
theorem observer_registered :
    extendedRegistry.protocol
      ((ProtocolRegistry.mergeRight baseRegistry observerRegistry
        scopes_disjoint).embed ()) = observer := rfl

end Grass.Process.Tests
