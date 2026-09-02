import Grass.Process.Progress
import Grass.Process.Run

/-!
# The application proof package

`docs/PROCESS.md` §4. This is the record an application author fills in, and its
size is the whole point: everything else in the process layer exists so that
this record stays small.

> Safety of memory, ABI, platform resources, concurrency, and raw instructions
> is not smuggled into `Invariant`; those remain independent lower-layer
> demands.

So `Invariant` is a predicate on `p.State` and on nothing else. There is no
field here about addresses, handles, threads, or instructions, and adding one
later would be the "safety afterthought" `docs/FOUNDATION.md` law 4 rejects.

## Two fields the normative document has that this record does not

`docs/PROCESS.md` §4 lists `terminalNoStep : NoProcessStepFromTerminal p` and,
separately, the generic `ProcessRun.observationCausality`. The second is not a
field here for the reason the document itself gives — "generic bookkeeping, not
an application proof field". It is `Reachable.observationCausality` in
`Grass/Process/Run.lean`, proved once over the segmentation that `Reachable`
carries as an index.

The first *is* a field here, and it is worth saying what it is not.
`ProcessRunTransition.not_from_terminal` says a run that has taken `terminate`
does not continue, and that is structural. `terminalNoStep` says something
independent: a state satisfying `p.Terminal` has no `p.Step` at all. Without it
a process could sit at a state its specification calls finished and keep
working, and a terminal-state theorem would say nothing about what the process
actually does there.

## Acceptance is a parameter

Every acceptance-shaped field is stated against a `ProcessAcceptance p` supplied
by the owner of the specification. See `Grass/Process/Acceptance.lean` for why
this layer must not construct one.
-/

namespace Grass.Process

universe u w

/--
The facts an application proves about one process.

`docs/PROCESS.md` §4: "Libraries provide induction/coinduction principles,
irrelevant-event stuttering, result correlation, cancellation, invariant framing,
and deterministic `update` simplification. A functional update proof normally
reduces to initial invariant, invariant preservation, view correctness, and
process progress."
-/
structure ProcessCorrect (p : ProcessSpec.{u, w}) (accept : ProcessAcceptance p) :
    Type (max (u + 1) (w + 1)) where
  /-- The application's own state invariant. Nothing lower-layer belongs here. -/
  Invariant : p.State → Prop
  /-- Every initial state satisfies it. -/
  initial : ∀ (request : p.Request) (state : p.State) (issued : Bag p.Demand)
      (emitted : p.Segment),
    p.Initial request state issued emitted → Invariant state
  /-- Every initially issued demand bag is well formed. -/
  initialDemands : ∀ (request : p.Request) (state : p.State)
      (issued : Bag p.Demand) (emitted : p.Segment),
    p.Initial request state issued emitted → accept.DemandsWellFormed issued
  /-- Every step preserves it. -/
  preserved : ∀ (state after : p.State) (event : p.Event)
      (issued : Bag p.Demand) (emitted : p.Segment),
    Invariant state → p.Step state event after issued emitted → Invariant after
  /-- Every demand bag a step issues is well formed. -/
  demandsWellFormed : ∀ (state after : p.State) (event : p.Event)
      (issued : Bag p.Demand) (emitted : p.Segment),
    Invariant state → p.Step state event after issued emitted →
    accept.DemandsWellFormed issued
  /-- Every reachable terminal result is one the specification accepts. -/
  terminal : ∀ (request : p.Request) (state : p.State) (result : p.TerminalResult),
    Invariant state → p.Terminal request state result →
    accept.TerminalAccepts request result
  /--
  A state the specification calls terminal does not step. See the module note
  for why this is not implied by `ProcessRunTransition.not_from_terminal`.
  -/
  terminalNoStep : ∀ (request : p.Request) (state after : p.State)
      (result : p.TerminalResult) (event : p.Event) (issued : Bag p.Demand)
      (emitted : p.Segment),
    p.Terminal request state result → ¬ p.Step state event after issued emitted
  /-- If the process has a view, every invariant-satisfying render is accepted. -/
  viewAccepts : ∀ (facet : ViewFacet p.State), p.view = some facet →
    ∀ state : p.State, Invariant state → accept.ViewAccepts facet (facet.render state)
  /--
  Every reachable observation prefix is accepted.

  Over prefixes, per `Grass/Process/Acceptance.lean`: this is the safety half.
  -/
  observationsAccept : ∀ (request : p.Request)
      (segmented : Segmented p.Observation) (runState : ProcessRunState p request),
    Reachable accept.terminalRemainder request segmented runState →
    accept.TraceAccepts runState.history
  /-- The process meets its progress contract, for every request. -/
  progress : ∀ request : p.Request,
    MeetsProcessProgress p accept Invariant request

namespace ProcessCorrect

variable {p : ProcessSpec.{u, w}} {accept : ProcessAcceptance p}
  {request : p.Request}

/--
Every reachable state satisfies the invariant.

This is the induction an author does not write. `docs/PROCESS.md` §4 promises
that "a functional update proof normally reduces to initial invariant, invariant
preservation, view correctness, and process progress"; this theorem is what
turns the first two of those into a statement about runs.
-/
theorem invariant_of_reachable (correct : ProcessCorrect p accept)
    {segmented : Segmented p.Observation} {runState : ProcessRunState p request}
    (reached : Reachable accept.terminalRemainder request segmented runState) :
    correct.Invariant runState.state := by
  induction reached with
  | initial isInitial =>
    cases isInitial with
    | running initial => exact correct.initial _ _ _ _ initial
  | initialTerminal isInitial =>
    cases isInitial with
    | terminal initial _ _ => exact correct.initial _ _ _ _ initial
  | step _ transition _ ih =>
    cases transition with
    | step _ stepped => exact correct.preserved _ _ _ _ _ ih stepped
    | settle _ _ stepped => exact correct.preserved _ _ _ _ _ ih stepped
    | terminate _ _ => exact ih

/--
Every reachable terminal state carries a result the specification accepts.

The composition of `invariant_of_reachable` with the `terminal` field. It is the
form a caller wants — "if this process finished, its answer was legitimate" —
and stating it here means the caller does not redo the induction.
-/
theorem terminalAccepts_of_reachable (correct : ProcessCorrect p accept)
    {segmented : Segmented p.Observation} {state : p.State}
    {result : p.TerminalResult} {observations : Trace p.Observation}
    (reached : Reachable accept.terminalRemainder request segmented
      (.terminal state result observations))
    (isTerminal : p.Terminal request state result) :
    accept.TerminalAccepts request result :=
  correct.terminal request state result
    (by simpa using correct.invariant_of_reachable reached) isTerminal

/--
A reachable state that the specification calls terminal cannot step.

The combination of the `terminalNoStep` field with reachability: it is the fact
a driver needs when it decides whether a dispatch loop may exit.
-/
theorem no_step_at_terminal (correct : ProcessCorrect p accept)
    {state after : p.State} {result : p.TerminalResult} {event : p.Event}
    {issued : Bag p.Demand} {emitted : p.Segment}
    (isTerminal : p.Terminal request state result) :
    ¬ p.Step state event after issued emitted :=
  correct.terminalNoStep request state after result event issued emitted isTerminal

end ProcessCorrect

end Grass.Process
