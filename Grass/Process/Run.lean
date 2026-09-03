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
| no replay | the successor's bag is `remainder + issued`, not `outstanding + issued` — see below |
| no joint consumption | one equation removes one `cons`, whatever the multiplicity |
| no silent loss | `remainder` is the whole rest of the bag |
| every remainder classified | `terminate` carries a bag *partition*, not a predicate |
| only `running` steps | no constructor has a `terminal` source state |

"No replay" is the one row that needs a qualification. The mechanism is exactly
as stated — the consumed occurrence is removed before the issued bag is added —
but the invariant a reader may infer from the word, that a result strictly
reduces its demand's multiplicity, is false: `issued` may contain the demand
just consumed, so a `.result` step can leave the run state bit-for-bit
identical. `Grass/Process/Progress.lean` is what stops such a step counting as
progress, not this table — its measure ranks the state *and the outstanding bag*
together, and a well-founded order is irreflexive, so a step that moves neither
cannot descend it.

The mechanism named here has been wrong twice, in the same sentence, and both
times a reviewer caught it by building the step rather than by reading. First it
named a `StepProgresses` disjunct that fired on the event's label
(`Tests/Process/SpinFixtures.lean` is the process that exploited it). Then it
named the `issued.card = 0` condition that replaced it, which had itself been
replaced by the measure taking the bag
(`Tests/Process/OscillateFixtures.lean` is why). A cross-module claim about
another module's definition is worth exactly as much as the last time someone
checked it.

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

## The history is flat, and the segmentation is an index

A run state carries the concatenated trace. The segmentation is carried by
`Reachable`, as an index, and `Reachable.segmentation_flat` says the two agree.

Splitting them this way is not arbitrary. An acceptance relation must survive
refinement: when a role is replaced by a flattened subsystem, the *same*
observations are produced by a different number of process transitions, so an
acceptance stated over the segmentation would be broken by a replacement that
changes nothing observable. Acceptance therefore sees `runState.history` and
nothing else.

Causality is the opposite case. `docs/PROCESS.md` §4 requires the emitting
segment of each observation to be *retained* through "later weaving, flattening,
serialization, machine simulation, and projection", so it cannot be discarded.
Carrying it as an index of `Reachable` gives `Reachable.observationCausality`
without letting it reach an acceptance relation.

An earlier draft put `Segmented` inside `ProcessRunState`, which failed the
first test, and then deleted it from the run entirely, which failed the second.
-/

namespace Grass.Process

universe u w

variable {p : ProcessSpec.{u, w}} {law : TerminalRemainderLaw p} {request : p.Request}

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
ones whose custody is transferred, and the ones left pending, and the partition
as a whole must be permitted by the specification's `TerminalRemainderLaw`.

Two things are load-bearing here and they are different.

**The partition conserves occurrences.** `card_partition` below: five
outstanding `CommitBytes` occurrences are five across the three parts, not one
`CommitBytes` value. A classification by demand *value* would collapse them,
because `Bag.Mem` is multiplicity-blind by design.

**The law bounds them.** Conservation alone only makes the number visible; it is
`TerminalRemainderLaw.Accepts` that can refuse a partition with three pending
writes when the specification allows one. That is why the law takes the three
bags rather than a demand.

What this does *not* give is any inter-custodian fact. `transferred` names no
recipient, no escrow, and no affine resolve token, so nothing here prevents two
processes from each claiming the same interaction was transferred to them.
`docs/FOUNDATION.md` law 16's "at most one receive or disposition" and law 20's
no-double-counting are properties of the channel escrow, and they arrive with
`Grass/Process/Network/Channel.lean` in M2. This structure is the per-process
half.
-/
structure TerminalDemandClassification {p : ProcessSpec.{u, w}}
    (law : TerminalRemainderLaw p) (request : p.Request)
    (state : p.State) (result : p.TerminalResult)
    (outstanding : Bag p.Demand) where
  /-- The occurrences claimed answered, or whose effect is known complete. -/
  resolved : Bag p.Demand
  /-- The occurrences whose custody passes to another process or the driver. -/
  transferred : Bag p.Demand
  /-- The occurrences left unanswered. -/
  pending : Bag p.Demand
  /-- Every outstanding occurrence is in exactly one part, and none is invented. -/
  partition : outstanding = resolved + transferred + pending
  /-- The specification permits this partition at this terminal state. -/
  permitted : law.Accepts request state result resolved transferred pending

namespace TerminalDemandClassification

variable {p : ProcessSpec.{u, w}} {law : TerminalRemainderLaw p}
  {request : p.Request} {state : p.State} {result : p.TerminalResult}
  {outstanding : Bag p.Demand}

/--
Multiplicity is conserved: the three parts account for every occurrence,
counted.

This is what makes the partition more than a relabelling. Without it a
classification could claim to dispose of a bag while its parts held fewer
occurrences than the bag did.
-/
theorem card_partition
    (classification : TerminalDemandClassification law request state result outstanding) :
    outstanding.card =
      classification.resolved.card + classification.transferred.card +
        classification.pending.card := by
  obtain ⟨resolved, transferred, pending, partition, _⟩ := classification
  subst partition
  simp

/-- Every outstanding demand value appears in at least one part. -/
theorem mem_some_part
    (classification : TerminalDemandClassification law request state result outstanding)
    {demand : p.Demand} (live : demand ∈ outstanding) :
    demand ∈ classification.resolved ∨ demand ∈ classification.transferred ∨
      demand ∈ classification.pending := by
  rw [classification.partition] at live
  simpa [or_assoc] using live

/--
A run holding nothing terminates whenever the law permits the empty partition.

`docs/PROCESS.md` §3 requires that "uncancellable leaf processes gain no new
author obligation", and this is where that is true: with nothing outstanding,
the obligation is whatever the law says about three empty bags, which the strict
law grants outright.
-/
def empty (law : TerminalRemainderLaw p) (request : p.Request) (state : p.State)
    (result : p.TerminalResult)
    (permitted : law.Accepts request state result 0 0 0) :
    TerminalDemandClassification law request state result 0 where
  resolved := 0
  transferred := 0
  pending := 0
  partition := by simp
  permitted := permitted

/-- Under the strict law, a run may only terminate holding nothing. -/
theorem strict_forces_empty
    (classification :
      TerminalDemandClassification (TerminalRemainderLaw.strict p) request state result
        outstanding) :
    outstanding = 0 := by
  obtain ⟨resolved, transferred, pending, partition, permitted⟩ := classification
  obtain ⟨noResolved, noTransferred, noPending⟩ := permitted
  subst partition; subst noResolved; subst noTransferred; subst noPending
  simp

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
inductive ProcessRunInitial {p : ProcessSpec.{u, w}}
    (law : TerminalRemainderLaw p) (request : p.Request) :
    ProcessRunState p request → Prop
  | running {state : p.State} {issued : Bag p.Demand} {emitted : p.Segment}
      (initial : p.Initial request state issued emitted) :
      ProcessRunInitial law request (.running state issued emitted)
  | terminal {state : p.State} {issued : Bag p.Demand} {emitted : p.Segment}
      {result : p.TerminalResult}
      (initial : p.Initial request state issued emitted)
      (isTerminal : p.Terminal request state result)
      (classification :
        TerminalDemandClassification law request state result issued) :
      ProcessRunInitial law request (.terminal state result emitted)

/--
One step of a run.

See the module note for the two-constructor form and for the table mapping each
clause of `docs/PROCESS.md` §2 to a field.
-/
inductive ProcessRunTransition {p : ProcessSpec.{u, w}}
    (law : TerminalRemainderLaw p) (request : p.Request) :
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
      ProcessRunTransition law request
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
      ProcessRunTransition law request
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
        TerminalDemandClassification law request state result outstanding) :
      ProcessRunTransition law request
        (.running state outstanding observations)
        (.terminal state result observations)

namespace ProcessRunTransition

/-! ### The five stepping rules of `docs/PROCESS.md` §2 -/

theorem stepExternal {state after : p.State} {outstanding issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {event : p.ExternalEvent}
    (transition : p.Step state (.external event) after issued emitted) :
    ProcessRunTransition law request
      (.running state outstanding observations)
      (.running after (outstanding + issued) (observations ++ emitted)) :=
  .step (by simp) transition

theorem stepFault {state after : p.State} {outstanding issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {fault : p.LogicalFault}
    (transition : p.Step state (.fault fault) after issued emitted) :
    ProcessRunTransition law request
      (.running state outstanding observations)
      (.running after (outstanding + issued) (observations ++ emitted)) :=
  .step (by simp) transition

theorem stepEnvironmentViolation {state after : p.State}
    {outstanding issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {violation : p.EnvironmentViolation}
    (transition :
      p.Step state (.environmentViolation violation) after issued emitted) :
    ProcessRunTransition law request
      (.running state outstanding observations)
      (.running after (outstanding + issued) (observations ++ emitted)) :=
  .step (by simp) transition

theorem stepResult {state after : p.State}
    {outstanding remainder issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {demand : p.Demand} {result : p.Result demand}
    (consume : Bag.ConsumeExactlyOneMatching outstanding demand remainder)
    (transition : p.Step state (.result demand result) after issued emitted) :
    ProcessRunTransition law request
      (.running state outstanding observations)
      (.running after (remainder + issued) (observations ++ emitted)) :=
  .settle (by simp) consume transition

theorem stepInterrupted {state after : p.State}
    {outstanding remainder issued : Bag p.Demand}
    {observations : Trace p.Observation} {emitted : p.Segment}
    {demand : p.Demand} {reason : p.InterruptReason}
    (consume : Bag.ConsumeExactlyOneMatching outstanding demand remainder)
    (transition : p.Step state (.interrupted demand reason) after issued emitted) :
    ProcessRunTransition law request
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
    ¬ ProcessRunTransition law request (.terminal state result observations) after := by
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
    (transition : ProcessRunTransition law request
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
    (transition : ProcessRunTransition law request before after) :
    ∃ emitted, after.history = before.history ++ emitted := by
  cases transition with
  | step _ _ => exact ⟨_, rfl⟩
  | settle _ _ _ => exact ⟨_, rfl⟩
  | terminate _ _ => exact ⟨[], by simp⟩

end ProcessRunTransition

/--
The states reachable by a finite execution prefix, together with the
segmentation that produced their trace.

The `Segmented` index is what keeps `docs/PROCESS.md` §4's observation causality
available. It is an index rather than a field of the run state so that an
acceptance relation, which sees only `runState.history`, cannot branch on it —
see the module note.

Finite by construction: this is the prefix relation, and every statement about
maximal or infinite executions belongs to `Grass.Semantics`.
-/
inductive Reachable {p : ProcessSpec.{u, w}} (law : TerminalRemainderLaw p)
    (request : p.Request) :
    Segmented p.Observation → ProcessRunState p request → Prop
  | initial {state : p.State} {issued : Bag p.Demand} {emitted : p.Segment}
      (isInitial : ProcessRunInitial law request (.running state issued emitted)) :
      Reachable law request (Segmented.empty.emit emitted)
        (.running state issued emitted)
  | initialTerminal {state : p.State} {result : p.TerminalResult}
      {emitted : p.Segment}
      (isInitial : ProcessRunInitial law request (.terminal state result emitted)) :
      Reachable law request (Segmented.empty.emit emitted)
        (.terminal state result emitted)
  | step {segmented : Segmented p.Observation}
      {before after : ProcessRunState p request} {emitted : p.Segment}
      (prior : Reachable law request segmented before)
      (transition : ProcessRunTransition law request before after)
      (exact : after.history = before.history ++ emitted) :
      Reachable law request (segmented.emit emitted) after

namespace Reachable

/--
The carried segmentation flattens to exactly the state's history.

The invariant that makes the index meaningful rather than decorative: without
it, `Reachable` could carry any segmentation at all and the causality theorem
below would say nothing about this run.
-/
theorem segmentation_flat {segmented : Segmented p.Observation}
    {runState : ProcessRunState p request}
    (reached : Reachable law request segmented runState) :
    segmented.flat = runState.history := by
  induction reached with
  | initial _ => simp
  | initialTerminal _ => simp
  | step _ _ exact ih => simp [exact, ih]

/--
**Observation causality.** Every observation occurrence in a reachable run's
trace was emitted by exactly one transition of that run.

`docs/PROCESS.md` §4 calls this "generic bookkeeping, not an application proof
field", and this is where that promise is kept: an author supplies nothing, and
the fact survives because `Reachable` carries the segmentation.

The conclusion is `Segmented.origin`'s decomposition, and `Segmented.origin_unique`
says that decomposition is the only one.
-/
theorem observationCausality {segmented : Segmented p.Observation}
    {runState : ProcessRunState p request}
    (reached : Reachable law request segmented runState)
    {observation : p.Observation} {before after : Trace p.Observation}
    (locate : runState.history = before ++ observation :: after) :
    ∃ segmentsBefore segment segmentsAfter segmentBefore segmentAfter,
      segmented.segments = segmentsBefore ++ segment :: segmentsAfter ∧
      segment = segmentBefore ++ observation :: segmentAfter ∧
      before = segmentsBefore.flatten ++ segmentBefore ∧
      after = segmentAfter ++ segmentsAfter.flatten :=
  segmented.origin (by rw [reached.segmentation_flat, locate])

/--
The emitting segment is the only one.

`observationCausality` produces a decomposition; this says no other decomposition
of the same run at the same position exists. Together they are
`docs/PROCESS.md` §4's "exactly one", which the existence half alone does not
give — a trace may contain the same observation value many times, so an
existential over values would identify no particular emission.
-/
theorem observationCausality_unique {segmented : Segmented p.Observation}
    {observation : p.Observation} {before : Trace p.Observation}
    {leftSegmentsBefore leftSegmentsAfter rightSegmentsBefore rightSegmentsAfter :
      List (ObservationSegment p.Observation)}
    {leftSegment rightSegment : ObservationSegment p.Observation}
    {leftSegmentBefore leftSegmentAfter rightSegmentBefore rightSegmentAfter :
      Trace p.Observation}
    (leftSplit : segmented.segments =
      leftSegmentsBefore ++ leftSegment :: leftSegmentsAfter)
    (leftInner : leftSegment = leftSegmentBefore ++ observation :: leftSegmentAfter)
    (leftBefore : before = leftSegmentsBefore.flatten ++ leftSegmentBefore)
    (rightSplit : segmented.segments =
      rightSegmentsBefore ++ rightSegment :: rightSegmentsAfter)
    (rightInner : rightSegment = rightSegmentBefore ++ observation :: rightSegmentAfter)
    (rightBefore : before = rightSegmentsBefore.flatten ++ rightSegmentBefore) :
    leftSegmentsBefore = rightSegmentsBefore ∧ leftSegment = rightSegment ∧
      leftSegmentsAfter = rightSegmentsAfter :=
  segmented.origin_unique leftSplit leftInner leftBefore rightSplit rightInner
    rightBefore

/--
One segment per transition, including the silent ones.

`segments.length` is the number of steps taken, which is exactly why it must not
reach an acceptance relation, and exactly why it is available to a causality
argument that needs to name a transition.
-/
theorem segment_count {segmented : Segmented p.Observation}
    {runState : ProcessRunState p request}
    (reached : Reachable law request segmented runState) :
    0 < segmented.segments.length := by
  induction reached with
  | initial _ => simp
  | initialTerminal _ => simp
  | step _ _ _ ih => simp

end Reachable

end Grass.Process
