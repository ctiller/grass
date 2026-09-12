import Grass.Target.Machine

/-!
# Adequacy from an inductive invariant

The machine tier's `Adequate` obligation says every admitted input starts an
execution and every reachable frontier completes: it either reaches `halted`
or continues forever. `adequate_of_invariant` derives that obligation from
input coverage and an `Invariant` that excludes stuck states:

- it holds in every initial state,
- every step preserves it, and
- every state satisfying it is halted or has a successor.

This is the shape a block-structured assembly verifier produces: block
contracts at labels, preserved by the instructions between them, with every
instruction's precondition (decodable, in bounds, authorized, platform call
realized) implied by the invariant. Proving a program safe is supplying that
invariant; the theorems here do the rest.

The completion argument is classical: if no finite continuation halts, a
successor is chosen at every step to build an infinite one.
-/

namespace Grass.Target.Machine

open Grass.Service

variable {isa : ISA} {D : Domain} (platform : Platform isa D) (raw : isa.Raw)

/-- An inductive invariant of the generic machine that excludes stuck states. -/
structure Invariant where
  Inv : State isa D platform → Prop
  initial : ∀ state, (system platform raw).Initial state () → Inv state
  preserved : ∀ {state choice event next}, Inv state →
    Step platform state choice event next → Inv next
  progress : ∀ state, Inv state →
    state.phase = .halted ∨ ∃ choice event next, Step platform state choice event next

variable {platform raw}

/-- The invariant holds along every coherent suffix from a state where it holds. -/
theorem Invariant.of_steps (inv : Invariant platform raw)
    {state next : (system platform raw).State} {graph graph' : (system platform raw).Graph}
    {events : List (Event D)} (holds : inv.Inv state)
    (steps : (system platform raw).Steps state graph events next graph') : inv.Inv next := by
  induction steps with
  | refl => exact holds
  | step _ transition ih => exact inv.preserved ih transition

/-- The invariant holds at the frontier of every execution prefix. -/
theorem Invariant.of_runs (inv : Invariant platform raw)
    {initial state : (system platform raw).State} {graph graph' : (system platform raw).Graph}
    {events : List (Event D)} (runs : (system platform raw).Runs initial graph state graph' events) : inv.Inv state := by
  induction runs with
  | initial valid => exact inv.initial _ valid
  | step _ transition ih => exact inv.preserved ih transition

/-- Iterate a function. -/
def iterate {α : Type} (f : α → α) (start : α) : Nat → α
  | 0 => start
  | n + 1 => f (iterate f start n)

/-- A chosen successor of a reachable non-halted state. -/
structure Successor (inv : Invariant platform raw) (origin : State isa D platform)
    (current : { state : State isa D platform //
      ∃ events, (system platform raw).Steps origin () events state () }) where
  choice : Choice D
  event : Event D
  next : { state : State isa D platform //
    ∃ events, (system platform raw).Steps origin () events state () }
  step : Step platform current.1 choice event next.1

/-- If no finite continuation from `origin` halts, every reachable state has a
successor. -/
theorem successor_nonempty (inv : Invariant platform raw)
    {origin : State isa D platform} (holds : inv.Inv origin)
    (neverHalts : ¬ ∃ events state, (system platform raw).Steps origin () events state () ∧
      state.phase = .halted)
    (current : { state : State isa D platform //
      ∃ events, (system platform raw).Steps origin () events state () }) :
    Nonempty (Successor inv origin current) := by
  obtain ⟨state, events, steps⟩ := current
  have invHere : inv.Inv state := inv.of_steps holds steps
  rcases inv.progress state invHere with halted | ⟨choice, event, next, step⟩
  · exact absurd ⟨events, state, steps, halted⟩ neverHalts
  · exact ⟨⟨choice, event, ⟨next, events ++ [event], .step steps step⟩, step⟩⟩

/-- Every frontier of the relabeled behavior completes, given an invariant
that excludes stuck states. -/
theorem completion_of_invariant (inv : Invariant platform raw) (spec : SpecRoot)
    (eventOf : Event D → spec.AuditEvent) (inputOf : platform.Environment → spec.Input)
    (run : (behavior platform raw spec eventOf inputOf).system.ExecutionPrefix) :
    Nonempty ((behavior platform raw spec eventOf inputOf).system.Completion
      run.state run.graph run.events) := by
  classical
  -- The relabeled prefix induces a raw prefix ending at the same state.
  have rawRuns : ∃ rawEvents, (system platform raw).Runs run.initialState ()
      run.state () rawEvents := by
    obtain ⟨initialState, initialGraph, state, graph, events, runs⟩ := run
    induction runs with
    | initial valid => exact ⟨[], .initial valid⟩
    | step _ transition ih =>
        obtain ⟨rawEvents, rawRuns⟩ := ih
        obtain ⟨rawEvent, rawStep, _⟩ := transition
        exact ⟨rawEvents ++ [rawEvent], .step rawRuns rawStep⟩
  obtain ⟨_, rawRuns⟩ := rawRuns
  have holds : inv.Inv run.state := inv.of_runs rawRuns
  by_cases halts : ∃ events state, (system platform raw).Steps run.state () events state () ∧
      state.phase = .halted
  · -- A finite raw continuation halts; relabel it.
    obtain ⟨events, final, steps, halted⟩ := halts
    have relabeled : ∀ {events final : _} {g g' : Unit},
        (system platform raw).Steps run.state g events final g' →
        (behavior platform raw spec eventOf inputOf).system.Steps run.state g
          (events.map eventOf) final g' := by
      intro events final g g' steps
      induction steps with
      | refl => exact .refl
      | step _ transition ih =>
          rw [List.map_append, List.map_singleton]
          exact .step ih ⟨_, transition, rfl⟩
    exact ⟨.finite (relabeled steps) halted⟩
  · -- No finite continuation halts: choose successors forever.
    let Reachable := { state : State isa D platform //
      ∃ events, (system platform raw).Steps run.state () events state () }
    have pick : ∀ current : Reachable, Successor inv run.state current :=
      fun current => Classical.choice (successor_nonempty inv holds halts current)
    let start : Reachable := ⟨run.state, [], .refl⟩
    let advance : Reachable → Reachable := fun current => (pick current).next
    let chain : Nat → Reachable := iterate advance start
    have graphEq : run.graph = () := rfl
    refine ⟨.infinite {
      stateAt := fun index => (chain index).1
      graphAt := fun _ => ()
      choiceAt := fun index => (pick (chain index)).choice
      eventAt := fun index => eventOf (pick (chain index)).event
      stateZero := rfl
      graphZero := graphEq.symm
      step := fun index => ⟨(pick (chain index)).event, (pick (chain index)).step, rfl⟩
      consistent := trivial }⟩

/-- Every admitted input starts an execution, given that the platform admits
an environment presenting it. -/
theorem execution_of_covers (spec : SpecRoot)
    (eventOf : Event D → spec.AuditEvent) (inputOf : platform.Environment → spec.Input)
    (covers : ∀ input, spec.admits input →
      ∃ env, platform.Admits env ∧ inputOf env = input)
    (input : spec.Input) (admitted : spec.admits input) :
    Nonempty { run : (behavior platform raw spec eventOf inputOf).system.ExecutionPrefix //
      (behavior platform raw spec eventOf inputOf).HasInput input run } := by
  obtain ⟨env, admits, presents⟩ := covers input admitted
  refine ⟨⟨RelationalSystem.ExecutionPrefix.initial
    (system := (behavior platform raw spec eventOf inputOf).system)
    (state := ⟨env, env, .running (isa.initial raw (platform.entry env))⟩) (graph := ())
    ⟨admits, rfl, rfl⟩, ?_⟩⟩
  exact presents

/-- Adequacy of the generic machine from an invariant and input coverage. This
is the whole machine-tier safety obligation for every ISA and platform. -/
theorem adequate_of_invariant (inv : Invariant platform raw) (spec : SpecRoot)
    (eventOf : Event D → spec.AuditEvent) (inputOf : platform.Environment → spec.Input)
    (covers : ∀ input, spec.admits input →
      ∃ env, platform.Admits env ∧ inputOf env = input) :
    (behavior platform raw spec eventOf inputOf).Adequate where
  execution := execution_of_covers spec eventOf inputOf covers
  completion := completion_of_invariant inv spec eventOf inputOf

end Grass.Target.Machine
