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
| every remainder classified | `terminate` carries a bag *partition*, not a predicate |
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

## The history is flat

A run state carries the concatenated trace, not its segmentation. An earlier
draft carried `Segmented`, which was wrong: `segments.length` is the number of
transitions taken, so an acceptance relation handed a segmented history could
distinguish one transition emitting `[a, b]` from two emitting `[a]` and `[b]`.
`docs/FOUNDATION.md` law 18 makes that batching a replaceable realization
choice, and law 19 forbids a consumer from assuming provider call boundaries are
message boundaries. `Segmented` and its origin theorems stay in
`Grass/Process/Observation.lean`, for the run-level causality bookkeeping that
`docs/PROCESS.md` §4 keeps out of the application proof.
-/

namespace Grass.Process

universe u w

variable {p : ProcessSpec.{u, w}} {request : p.Request}

/--
The state of a run in progress or finished.

The history is finite because it is the history of a finite prefix. A *maximal*
run need not be finite, and no definition here assumes it is; see
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.2.
-/
inductive ProcessRunState (p : ProcessSpec.{u, w}) (request : p.Request) :
    Type (max u w)
  /-- Live: local state, the outstanding demand bag, and the trace so far. -/
  | running (state : p.State) (outstanding : Bag p.Demand)
      (observations : Trace p.Observation)
  /-- Finished: the terminal state, its typed result, and the final trace. -/
  | terminal (state : p.State) (result : p.TerminalResult)
      (observations : Trace p.Observation)

namespace ProcessRunState

/-- The local process state a run state holds, live or finished. -/
def state : ProcessRunState p request → p.State
  | .running state _ _ => state
  | .terminal state _ _ => state

/-- The observation history a run state holds, live or finished. -/
def history : ProcessRunState p request → Trace p.Observation
  | .running _ _ observations => observations
  | .terminal _ _ observations => observations

@[simp] theorem state_running (state : p.State) (outstanding : Bag p.Demand)
    (observations : Trace p.Observation) :
    (ProcessRunState.running (request := request) state outstanding
      observations).state = state := rfl

@[simp] theorem state_terminal (state : p.State) (result : p.TerminalResult)
    (observations : Trace p.Observation) :
    (ProcessRunState.terminal (request := request) state result
      observations).state = state := rfl

@[simp] theorem history_running (state : p.State) (outstanding : Bag p.Demand)
    (observations : Trace p.Observation) :
    (ProcessRunState.running (request := request) state outstanding
      observations).history = observations := rfl

@[simp] theorem history_terminal (state : p.State) (result : p.TerminalResult)
    (observations : Trace p.Observation) :
    (ProcessRunState.terminal (request := request) state result
      observations).history = observations := rfl

end ProcessRunState

/--
A terminal transition's account of every demand still outstanding.

The outstanding bag is *partitioned* into the occurrences claimed resolved, the
ones whose custody is transferred, and the ones the specification permits to
remain pending; each part must be permitted by `p.TerminalDisposition`.

A partition rather than a function from demand values to dispositions. That
distinction is the whole enforcement of `docs/FOUNDATION.md` law 7 here. With a
function, the obligation would depend only on the bag's *support*, because
`Bag.Mem` is multiplicity-blind by design: a process holding five outstanding
`CommitBytes` demands would discharge all five with a single claim about the
value `CommitBytes`. Under law 20 ("affine transfers are not double-counted")
and law 16 ("every occurrence has at most one receive or disposition") that is
exactly the accounting this layer exists to prevent. With the partition,
`card_partition` below shows that five occurrences are still five, distributed
across the three outcomes.

Within one part the permission is still stated on values, and that is correct:
whether `transferred` is a legitimate outcome for a `CommitBytes` demand at this
terminal state is a property of the demand and the state, not of which copy.
-/
structure TerminalDemandClassification (p : ProcessSpec.{u, w})
    (request : p.Request) (state : p.State) (result : p.TerminalResult)
    (outstanding : Bag p.Demand) where
  /-- The occurrences claimed answered, or whose effect is known complete. -/
  resolved : Bag p.Demand
  /-- The occurrences whose custody passes to another process or the driver. -/
  transferred : Bag p.Demand
  /-- The occurrences the specification permits to remain unanswered. -/
  pending : Bag p.Demand
  /-- Every outstanding occurrence is in exactly one part, and none is invented. -/
  partition : outstanding = resolved + transferred + pending
  /-- The specification permits `resolved` for each demand claimed resolved. -/
  resolvedPermitted : ∀ demand ∈ resolved,
    p.TerminalDisposition request state result demand .resolved
  /-- The specification permits `transferred` for each demand transferred. -/
  transferredPermitted : ∀ demand ∈ transferred,
    p.TerminalDisposition request state result demand .transferred
  /-- The specification permits `permittedPending` for each demand left pending. -/
  pendingPermitted : ∀ demand ∈ pending,
    p.TerminalDisposition request state result demand .permittedPending

namespace TerminalDemandClassification

variable {state : p.State} {result : p.TerminalResult} {outstanding : Bag p.Demand}

/--
Multiplicity is conserved: the three parts account for every occurrence,
counted.

This is the theorem that makes the partition load-bearing rather than
decorative. A resource or obligation law downstream reads `transferred` and gets
the true number of custody transfers, not the number of distinct demand values.
-/
theorem card_partition
    (classification : TerminalDemandClassification p request state result outstanding) :
    outstanding.card =
      classification.resolved.card + classification.transferred.card +
        classification.pending.card := by
  obtain ⟨resolved, transferred, pending, partition, _, _, _⟩ := classification
  subst partition
  simp

/-- Every outstanding demand value appears in at least one part. -/
theorem mem_some_part
    (classification : TerminalDemandClassification p request state result outstanding)
    {demand : p.Demand} (live : demand ∈ outstanding) :
    demand ∈ classification.resolved ∨ demand ∈ classification.transferred ∨
      demand ∈ classification.pending := by
  rw [classification.partition] at live
  simpa [or_assoc] using live

/--
Every outstanding demand has a permitted disposition.

The form `docs/PROCESS.md` §2 states — "termination explicitly resolves,
transfers, or permits pending for every remainder" — recovered from the
partition, so a consumer that only needs the coverage fact does not have to
unfold it.
-/
theorem covered
    (classification : TerminalDemandClassification p request state result outstanding)
    {demand : p.Demand} (live : demand ∈ outstanding) :
    ∃ disposition, p.TerminalDisposition request state result demand disposition := by
  rcases classification.mem_some_part live with inResolved | inTransferred | inPending
  · exact ⟨.resolved, classification.resolvedPermitted demand inResolved⟩
  · exact ⟨.transferred, classification.transferredPermitted demand inTransferred⟩
  · exact ⟨.permittedPending, classification.pendingPermitted demand inPending⟩

/--
A run holding nothing terminates with the empty classification.

Not a convenience: it is the statement that law 7 costs an author nothing when
there is nothing outstanding, which is the common case and should not require a
constructed witness.
-/
def empty (p : ProcessSpec.{u, w}) (request : p.Request) (state : p.State)
    (result : p.TerminalResult) :
    TerminalDemandClassification p request state result 0 where
  resolved := 0
  transferred := 0
  pending := 0
  partition := by simp
  resolvedPermitted := by simp
  transferredPermitted := by simp
  pendingPermitted := by simp

end TerminalDemandClassification

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
inductive ProcessRunInitial (p : ProcessSpec.{u, w}) (request : p.Request) :
    ProcessRunState p request → Prop
  | running {state : p.State} {issued : Bag p.Demand} {emitted : p.Segment}
      (initial : p.Initial request state issued emitted) :
      ProcessRunInitial p request (.running state issued emitted)
  | terminal {state : p.State} {issued : Bag p.Demand} {emitted : p.Segment}
      {result : p.TerminalResult}
      (initial : p.Initial request state issued emitted)
      (isTerminal : p.Terminal request state result)
      (classification :
        TerminalDemandClassification p request state result issued) :
      ProcessRunInitial p request (.terminal state result emitted)

/--
One step of a run.

See the module note for the two-constructor form and for the table mapping each
clause of `docs/PROCESS.md` §2 to a field.
-/
inductive ProcessRunTransition (p : ProcessSpec.{u, w}) (request : p.Request) :
    ProcessRunState p request → ProcessRunState p request → Prop
  /--
  An event that settles no outstanding demand: external entropy, a fault, or an
  environment violation. The outstanding bag is preserved and extended.
  -/
  | step {state after : p.State} {outstanding issued : Bag p.Demand}
      {observations : Trace p.Observation} {emitted : p.Segment}
      {event : p.Event}
      (settlesNothing : event.settles = none)
      (transition : p.Step state event after issued emitted) :
      ProcessRunTransition p request
        (.running state outstanding observations)
        (.running after (outstanding + issued) (observations ++ emitted))
  /--
  An event that settles exactly one outstanding demand: a result or an
  interruption. The consumed occurrence is removed before the issued bag is
  added.
  -/
  | settle {state after : p.State}
      {outstanding remainder issued : Bag p.Demand}
      {observations : Trace p.Observation} {emitted : p.Segment}
      {event : p.Event} {demand : p.Demand}
      (settlesDemand : event.settles = some demand)
      (consume : Bag.ConsumeExactlyOneMatching outstanding demand remainder)
      (transition : p.Step state event after issued emitted) :
      ProcessRunTransition p request
        (.running state outstanding observations)
        (.running after (remainder + issued) (observations ++ emitted))
  /--
  Termination. Requires the request-indexed `Terminal` witness and a partition
  of every demand still outstanding into permitted dispositions. Emits nothing:
  the terminal state's observations are the history already accumulated.
  -/
  | terminate {state : p.State} {outstanding : Bag p.Demand}
      {observations : Trace p.Observation} {result : p.TerminalResult}
      (isTerminal : p.Terminal request state result)
      (classification :
        TerminalDemandClassification p request state result outstanding) :
      ProcessRunTransition p request
        (.running state outstanding observations)
        (.terminal state result observations)

namespace ProcessRunTransition

/-! ### The five stepping rules of `docs/PROCESS.md` §2 -/

theorem stepExternal {state after : p.State} {outstanding issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {event : p.ExternalEvent}
    (transition : p.Step state (.external event) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (outstanding + issued) (observations ++ emitted)) :=
  .step (by simp) transition

theorem stepFault {state after : p.State} {outstanding issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {fault : p.LogicalFault}
    (transition : p.Step state (.fault fault) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (outstanding + issued) (observations ++ emitted)) :=
  .step (by simp) transition

theorem stepEnvironmentViolation {state after : p.State}
    {outstanding issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {violation : p.EnvironmentViolation}
    (transition :
      p.Step state (.environmentViolation violation) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (outstanding + issued) (observations ++ emitted)) :=
  .step (by simp) transition

theorem stepResult {state after : p.State}
    {outstanding remainder issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {demand : p.Demand} {result : p.Result demand}
    (consume : Bag.ConsumeExactlyOneMatching outstanding demand remainder)
    (transition : p.Step state (.result demand result) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (remainder + issued) (observations ++ emitted)) :=
  .settle (by simp) consume transition

theorem stepInterrupted {state after : p.State}
    {outstanding remainder issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {demand : p.Demand} {reason : p.InterruptReason}
    (consume : Bag.ConsumeExactlyOneMatching outstanding demand remainder)
    (transition : p.Step state (.interrupted demand reason) after issued emitted) :
    ProcessRunTransition p request
      (.running state outstanding observations)
      (.running after (remainder + issued) (observations ++ emitted)) :=
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
    {observations : Trace p.Observation}
    {after : ProcessRunState p request} :
    ¬ ProcessRunTransition p request (.terminal state result observations) after := by
  intro transition; cases transition

/--
A stepping transition removes at most one outstanding occurrence.

The counting corollary of the two prohibitions in `docs/PROCESS.md` §2 that
concern the bag's size: only `settle` removes anything, and it removes exactly
one, so nothing can leave the bag two at a time.

It is a corollary and not the prohibition itself. "Cannot be silently lost" is
the stronger structural fact that `settle`'s `remainder` is the whole rest of
the bag rather than an arbitrary sub-bag, and it is
`Bag.ConsumeExactlyOneMatching` that says so. The inequality also says nothing
about `terminate`, which disposes of the entire remaining bag at once and is
governed by `TerminalDemandClassification` instead.
-/
theorem card_drops_by_at_most_one
    {state afterState : p.State} {outstanding afterOutstanding : Bag p.Demand}
    {observations afterObservations : Trace p.Observation}
    (transition : ProcessRunTransition p request
      (.running state outstanding observations)
      (.running afterState afterOutstanding afterObservations)) :
    outstanding.card ≤ afterOutstanding.card + 1 := by
  cases transition with
  | step _ _ => simp; omega
  | settle _ consume _ => simp [consume.card]

/--
Every transition extends the observation history; nothing is retracted.

`docs/PROCESS.md` §2: "revisiting or rendering a state cannot duplicate an
observation". The dual fact — that a transition cannot *un*-emit — is what makes
the history a prefix order, and it is what an acceptance relation stated over
prefixes relies on.
-/
theorem history_extends {before after : ProcessRunState p request}
    (transition : ProcessRunTransition p request before after) :
    ∃ emitted, after.history = before.history ++ emitted := by
  cases transition with
  | step _ _ => exact ⟨_, rfl⟩
  | settle _ _ _ => exact ⟨_, rfl⟩
  | terminate _ _ => exact ⟨[], by simp⟩

end ProcessRunTransition

/--
The states reachable by a finite execution prefix of `p` on `request`.

Finite by construction: this is the prefix relation, and every statement about
maximal or infinite executions belongs to `Grass.Semantics`.
-/
inductive Reachable (p : ProcessSpec.{u, w}) (request : p.Request) :
    ProcessRunState p request → Prop
  | initial {state : ProcessRunState p request}
      (isInitial : ProcessRunInitial p request state) : Reachable p request state
  | step {before after : ProcessRunState p request}
      (prior : Reachable p request before)
      (transition : ProcessRunTransition p request before after) :
      Reachable p request after

end Grass.Process
