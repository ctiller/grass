import Grass.Process.Spec

/-!
# Process runs

`docs/PROCESS.md` §2. `ProcessSpec.Step` says nothing about how many copies of a
demand are outstanding; the run relation is where multiplicity becomes linear:

> Equal demand values remain indistinguishable at the precious level, but their
> bag multiplicity cannot be fabricated, replayed, jointly consumed by one
> result, or silently lost. A result/interruption requires and consumes exactly
> one live matching item; termination explicitly resolves, transfers, or permits
> pending for every remainder according to the specification's
> progress/lifecycle law.

Each clause of that paragraph is a structural feature of the definitions below
rather than a side condition:

| Clause | Mechanism |
|---|---|
| no fabrication | `settle` requires `outstanding = cons demand remainder` |
| no replay | the successor's bag is `remainder + issued`, not `outstanding + issued` |
| no joint consumption | one equation removes one `cons`, whatever the multiplicity |
| no silent loss | `remainder` is the whole rest of the bag |
| every remainder classified | `terminate` carries a `TerminalDemandClassification` |
| only `running` steps | no constructor has a `terminal` source state |

## Two constructors, five derived rules

`docs/PROCESS.md` lists five stepping constructors — external, result,
interrupted, fault, environment violation — of which the middle two consume an
outstanding demand and the other three do not. That split is exactly
`ProcessEvent.settles`, so the definition here has two stepping constructors
indexed by it, and the document's five appear as the derived introduction rules
`stepExternal` through `stepEnvironmentViolation`. Eliminating in the document's
five cases is `cases` on the transition followed by `cases` on the event, whose
`settles` equation rules out three of the five branches on the spot.

This is not a shortcut. It is what makes the frame reasoning of
`Grass/Process/Weave/Mixin.lean` tractable later: a mixin that does not touch
the outstanding bag discharges one case, not three, and cannot accidentally omit
the fourth.
-/

namespace Grass.Process

universe u

variable {p : ProcessSpec.{u}} {request : p.Request}

/--
The state of a run in progress or finished.

The observation history is `Segmented`, not a bare trace, so that the segment
which emitted each observation survives into weaving, flattening, and machine
simulation. `docs/PROCESS.md` §4 calls this "generic bookkeeping, not an
application proof field".

The history is finite because it is the history of a finite prefix. A *maximal*
run need not be finite, and no definition here assumes it is; see
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.2.
-/
inductive ProcessRunState (p : ProcessSpec.{u}) (request : p.Request) : Type u
  /-- Live: local state, the outstanding demand bag, and the history so far. -/
  | running (state : p.State) (outstanding : Bag p.Demand)
      (observations : Segmented p.Observation)
  /-- Finished: the terminal state, its typed result, and the final history. -/
  | terminal (state : p.State) (result : p.TerminalResult)
      (observations : Segmented p.Observation)

namespace ProcessRunState

/-- The local process state a run state holds, live or finished. -/
def state : ProcessRunState p request → p.State
  | .running state _ _ => state
  | .terminal state _ _ => state

/-- The observation history a run state holds, live or finished. -/
def history : ProcessRunState p request → Segmented p.Observation
  | .running _ _ observations => observations
  | .terminal _ _ observations => observations

@[simp] theorem state_running (state : p.State) (outstanding : Bag p.Demand)
    (observations : Segmented p.Observation) :
    (ProcessRunState.running (request := request) state outstanding observations).state = state := rfl

@[simp] theorem state_terminal (state : p.State) (result : p.TerminalResult)
    (observations : Segmented p.Observation) :
    (ProcessRunState.terminal (request := request) state result observations).state = state := rfl

@[simp] theorem history_running (state : p.State) (outstanding : Bag p.Demand)
    (observations : Segmented p.Observation) :
    (ProcessRunState.running (request := request) state outstanding observations).history
      = observations := rfl

@[simp] theorem history_terminal (state : p.State) (result : p.TerminalResult)
    (observations : Segmented p.Observation) :
    (ProcessRunState.terminal (request := request) state result observations).history
      = observations := rfl

end ProcessRunState

/--
A terminal transition's account of every demand still outstanding.

`disposition` assigns one of the three outcomes to each demand value, and
`permitted` requires the specification to have allowed that outcome for that
demand at that terminal state. Without the second field this record would be
free — every terminal transition could map everything to `permittedPending` —
and `docs/FOUNDATION.md` law 7 would be unenforced.

The assignment is on demand *values* rather than on occurrences because at this
level equal demand values are indistinguishable, so a classification that
treated two copies differently would be observing an identity the precious layer
does not have.
-/
structure TerminalDemandClassification (p : ProcessSpec.{u}) (request : p.Request)
    (state : p.State) (result : p.TerminalResult) (outstanding : Bag p.Demand) where
  /-- The outcome claimed for each demand value. -/
  disposition : p.Demand → TerminalDemandDisposition
  /-- The specification permits that outcome, for every demand still live. -/
  permitted : ∀ demand ∈ outstanding,
    p.TerminalDisposition request state result demand (disposition demand)

/--
The initial states of a run.

`docs/PROCESS.md` §2: "`ProcessRunInitial` is the only initial form: it begins
from an empty prior history and exactly the state, initial demands, and
observations emitted by `Initial`."

The `terminal` constructor is what makes a zero-transition terminal run
genuinely terminal rather than a running state followed by a hidden transition.
It is available only when the initial state also satisfies `Terminal` and every
initially issued demand already has a permitted disposition.
-/
inductive ProcessRunInitial (p : ProcessSpec.{u}) (request : p.Request) :
    ProcessRunState p request → Prop
  | running {state : p.State} {issued : Bag p.Demand} {emitted : p.Segment}
      (initial : p.Initial request state issued emitted) :
      ProcessRunInitial p request
        (.running state issued (Segmented.empty.emit emitted))
  | terminal {state : p.State} {issued : Bag p.Demand} {emitted : p.Segment}
      {result : p.TerminalResult}
      (initial : p.Initial request state issued emitted)
      (isTerminal : p.Terminal request state result)
      (classification :
        TerminalDemandClassification p request state result issued) :
      ProcessRunInitial p request
        (.terminal state result (Segmented.empty.emit emitted))

/--
One step of a run.

See the module note for the two-constructor form and for the table mapping each
clause of `docs/PROCESS.md` §2 to a field.
-/
inductive ProcessRunTransition (p : ProcessSpec.{u}) (request : p.Request) :
    ProcessRunState p request → ProcessRunState p request → Prop
  /--
  An event that settles no outstanding demand: external entropy, a fault, or an
  environment violation. The outstanding bag is preserved and extended.
  -/
  | step {state after : p.State} {outstanding issued : Bag p.Demand}
      {observations : Segmented p.Observation} {emitted : p.Segment}
      {event : p.Event}
      (settlesNothing : event.settles = none)
      (transition : p.Step state event after issued emitted) :
      ProcessRunTransition p request
        (.running state outstanding observations)
        (.running after (outstanding + issued) (observations.emit emitted))
  /--
  An event that settles exactly one outstanding demand: a result or an
  interruption. The consumed occurrence is removed before the issued bag is
  added.
  -/
  | settle {state after : p.State}
      {outstanding remainder issued : Bag p.Demand}
      {observations : Segmented p.Observation} {emitted : p.Segment}
      {event : p.Event} {demand : p.Demand}
      (settlesDemand : event.settles = some demand)
      (consume : Bag.ConsumeExactlyOneMatching outstanding demand remainder)
      (transition : p.Step state event after issued emitted) :
      ProcessRunTransition p request
        (.running state outstanding observations)
        (.running after (remainder + issued) (observations.emit emitted))
  /--
  Termination. Requires the request-indexed `Terminal` witness and a permitted
  disposition for every demand still outstanding. Emits nothing: the terminal
  state's observations are the history already accumulated.
  -/
  | terminate {state : p.State} {outstanding : Bag p.Demand}
      {observations : Segmented p.Observation} {result : p.TerminalResult}
      (isTerminal : p.Terminal request state result)
      (classification :
        TerminalDemandClassification p request state result outstanding) :
      ProcessRunTransition p request
        (.running state outstanding observations)
        (.terminal state result observations)

namespace ProcessRunTransition

/-! ### The five stepping rules of `docs/PROCESS.md` §2 -/

theorem stepExternal {state after : p.State} {outstanding issued : Bag p.Demand}
    {observations : Segmented p.Observation} {emitted : p.Segment}
    {event : p.ExternalEvent}
    (transition : p.Step state (.external event) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (outstanding + issued) (observations.emit emitted)) :=
  .step (by simp) transition

theorem stepFault {state after : p.State} {outstanding issued : Bag p.Demand}
    {observations : Segmented p.Observation} {emitted : p.Segment}
    {fault : p.LogicalFault}
    (transition : p.Step state (.fault fault) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (outstanding + issued) (observations.emit emitted)) :=
  .step (by simp) transition

theorem stepEnvironmentViolation {state after : p.State}
    {outstanding issued : Bag p.Demand}
    {observations : Segmented p.Observation} {emitted : p.Segment}
    {violation : p.EnvironmentViolation}
    (transition :
      p.Step state (.environmentViolation violation) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (outstanding + issued) (observations.emit emitted)) :=
  .step (by simp) transition

theorem stepResult {state after : p.State}
    {outstanding remainder issued : Bag p.Demand}
    {observations : Segmented p.Observation} {emitted : p.Segment}
    {demand : p.Demand} {result : p.Result demand}
    (consume : Bag.ConsumeExactlyOneMatching outstanding demand remainder)
    (transition : p.Step state (.result demand result) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (remainder + issued) (observations.emit emitted)) :=
  .settle (by simp) consume transition

theorem stepInterrupted {state after : p.State}
    {outstanding remainder issued : Bag p.Demand}
    {observations : Segmented p.Observation} {emitted : p.Segment}
    {demand : p.Demand} {reason : p.InterruptReason}
    (consume : Bag.ConsumeExactlyOneMatching outstanding demand remainder)
    (transition : p.Step state (.interrupted demand reason) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (remainder + issued) (observations.emit emitted)) :=
  .settle (by simp) consume transition

/-! ### Structural facts -/

/--
Only `running` states step.

`docs/PROCESS.md` §2: a terminal transition "has no outgoing transition". No
constructor above has a terminal source, so this is structural and no author
proves it.

It is *not* the `terminalNoStep` field of `ProcessCorrect`, and conflating the
two would be a real loss. This theorem says a run that has taken `terminate`
does not continue. `terminalNoStep` says something stronger and independent: a
state satisfying `p.Terminal` has no `p.Step` at all, so a process cannot sit at
a finishing state and keep working. That one is an application obligation and is
a field of `Grass/Process/Correct.lean`.
-/
theorem not_from_terminal {state : p.State} {result : p.TerminalResult}
    {observations : Segmented p.Observation}
    {after : ProcessRunState p request} :
    ¬ ProcessRunTransition p request (.terminal state result observations) after := by
  intro transition; cases transition

/--
A transition removes at most one outstanding occurrence.

This is the counting form of the two prohibitions in `docs/PROCESS.md` §2 that
concern the bag's size. "Cannot be jointly consumed by one result" is the
statement that no single transition removes two occurrences of an equal demand
value; "cannot be silently lost" is the statement that no transition removes an
occurrence without settling it. Both are the same inequality, because the only
constructor that removes anything is `settle`, and it removes exactly one.

It is stated over the transition rather than over its hypotheses so that it
holds for the family, not only for a transition an author happened to build with
a particular rule.
-/
theorem card_drops_by_at_most_one
    {state afterState : p.State} {outstanding afterOutstanding : Bag p.Demand}
    {observations afterObservations : Segmented p.Observation}
    (transition : ProcessRunTransition p request
      (.running state outstanding observations)
      (.running afterState afterOutstanding afterObservations)) :
    outstanding.card ≤ afterOutstanding.card + 1 := by
  cases transition with
  | step _ _ => simp; omega
  | settle _ consume _ => simp [consume.card]

end ProcessRunTransition

/--
The states reachable by a finite execution prefix of `p` on `request`.

Finite by construction: this is the prefix relation, and every statement about
maximal or infinite executions belongs to `Grass.Semantics`.
-/
inductive Reachable (p : ProcessSpec.{u}) (request : p.Request) :
    ProcessRunState p request → Prop
  | initial {state : ProcessRunState p request}
      (isInitial : ProcessRunInitial p request state) : Reachable p request state
  | step {before after : ProcessRunState p request}
      (prior : Reachable p request before)
      (transition : ProcessRunTransition p request before after) :
      Reachable p request after

end Grass.Process
