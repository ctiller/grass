import Grass.Process.Acceptance
import Grass.Process.Run

/-!
# Per-process progress

`docs/PROCESS.md` §7:

> A process cycle must:
>
> - decrease a well-founded internal measure;
> - reach a law-bearing external/demand-result frontier in finite internal
>   work; or
> - produce an independently specified observation.

and, immediately after:

> Local progress is necessary but insufficient. `ProcessNetworkAdequate` proves
> the corresponding theorem over every maximal network execution.

This module owns the first statement only. The network theorem is M4 work in
`docs/PROCESS_IMPLEMENTATION_PLAN.md`, and nothing here should be mistaken for
it.

## Reading the four disjuncts at this layer

Every `ProcessRunTransition` consumes an event, so a single process never takes
an internal step of its own accord; the internal work §7 refers to happens
*inside* one transition, in a serial call or in the machine realization, and the
finite-internal-work clause is discharged there. What remains at this layer is a
sharper question: which arriving events came from outside the program, and which
are the program's own activity coming back?

`ProcessEvent.externalEntropy` answers it, and `settles` does not. An earlier
draft used `settles = none` as the frontier disjunct, which gave `.fault` and
`.environmentViolation` a free pass: a process that faults in a loop, emits
nothing, and decreases no measure satisfied the condition. A fault is the
process failing, not the environment speaking — `Grass/Process/Vocabulary.lean`
lists them as separate constructors for exactly that reason — so only
`.external` counts as waiting.

So `StepProgresses` is: environment entropy arrived, **or** an outstanding
demand was answered and no new one issued in its place, **or** the transition
emitted an observation the specification demanded, **or** a well-founded measure
strictly decreased. A server's accept loop satisfies the third disjunct on every
connection. A silent fault loop satisfies none, and neither does a silent
demand-*reissuing* spin — `reissuing_step_decreases` is the theorem that says so.

The second disjunct's `issued` condition is the whole of its content, and it went
in without one. §7's "demand-result frontier" reads as though answering a
demand is progress on its own, and it is not: a step that consumes one occurrence
and issues another leaves the outstanding bag the same size, and if the state and
the trace are also unchanged the run has returned to where it started. Local
adversarial review built exactly that process — one demand, one step, an empty
`ExternalEvent` so it could not even use the entropy escape below — and gave it a
full `ProcessCorrect` with a constant measure.
`Tests/Process/SpinFixtures.lean` keeps it, and keeps the proof that it is now
excluded.

Two honest limits. First, this layer has no way to say which frontiers are
*law-bearing* in §7's sense: `ProcessAcceptance` carries no frontier
declaration, so "waiting forever for entropy that never comes" passes here, and
is excluded — if at all — by the network adequacy theorem. Second,
`StepProgresses` reads the transition's own emitted segment. That is sound
because a `ProcessSpec.Step`'s segment is authored — §2 gives `Step` an
observation-segment output — but it also means progress is a per-specification
property, to be re-proved after a refinement changes the transition structure
rather than transported across it. Trace *acceptance*, which must transport,
sees only the flat history.

## Responsiveness is the other half, and it needs reachability

`docs/FOUNDATION.md` law 5 requires every admitted external or nondeterministic
result to be handled. A process whose `Step` relation has no successor is stuck,
and stuckness is not caught by any measure — a measure only constrains steps
that happen.

An earlier draft stated this over a state and an *independently quantified*
outstanding bag, which made it both too strong and too weak. Too strong, because
a caller could choose a bag containing a demand the process never issued and
force a successor for it. Too weak, because it never established that any
transition was available at all. It is now stated over reachable run states,
where the state and the bag come from the same execution.

The terminal disjunct had a hole worth naming. It was
`∃ result, p.Terminal request state result` — the specification's terminal
*predicate*, which does not by itself make `ProcessRunTransition.terminate`
available, because that constructor additionally needs a permitted disposition
of the outstanding bag. A specification could therefore declare a state
terminal, have no `Step`, and permit no disposition, and the run would be
permanently stuck while every field was satisfied. The disjunct now demands the
classification, and `exists_transition` below is the proof that the hole is
closed.

`handlesEveryEvent` then needs its non-terminality guard, and the reason is
worth stating because the first version of it made this record *uninhabitable*.
`ProcessCorrect.terminalNoStep` forbids any `p.Step` from a state satisfying
`p.Terminal`. An unguarded `handlesEveryEvent` demands a `p.Step` at every
reachable running state — and the running state a terminating run fires
`terminate` from is reachable and terminal. The two fields contradicted each
other for every process that terminates other than immediately, so no
terminating process had a `ProcessCorrect` at all. Law 5 applies where the
process is still working; at a terminal state the obligation is to terminate,
which is `notStuck`'s left disjunct.

## What this layer still cannot exclude

The module note above records that "waiting forever for entropy that never
comes" passes, because nothing here declares which frontiers are law-bearing.
The dual passes too, and is worth naming: `ExternalEvent` is chosen by the
specification author, so a process can route its own internal work through a
self-delivered tick, satisfy the entropy disjunct forever, never terminate,
never emit, and never decrease its measure. A total livelock of that shape has a
`ProcessCorrect`.

**And the demand disjunct's escape is one step further out.** `issued.card = 0`
kills a one-demand spin, and a *two*-demand cycle evades it: `d`'s result issues
`e`, `e`'s result issues `d`, each step answering something and each issuing
something, the bag never growing, the state never moving. Excluding that needs a
well-founded order on the outstanding bag, which the bag's own cardinality cannot
supply because it is constant along the cycle. Nothing here can build one: the
demands are the specification's and their dependency structure is not declared.
Named rather than left implied; `docs/PROCESS_IMPLEMENTATION_PLAN.md` §6
carries it with the entropy escape.

Excluding it needs a frontier declaration — a statement that a given external
event is genuinely produced by the environment and not by the program — which
`ProcessAcceptance` does not carry and which this layer has no way to check.
`docs/PROCESS.md` §7 puts the burden on the network: "An infinite network run
must produce a specification-demanded observation or remain at a declared
external frontier". `docs/PROCESS_IMPLEMENTATION_PLAN.md` §6 records it as an M4
exit obligation rather than leaving it implied.
-/

namespace Grass.Process

universe u w

/--
A well-founded internal measure on process state.

`Rank` is a type rather than `Nat` because a lexicographic or structural measure
is normal for a state machine with phases, and forcing it through `Nat` costs an
encoding proof for nothing.
-/
structure ProcessMeasure (p : ProcessSpec.{u, w}) : Type (w + 1) where
  /-- The ordered carrier. -/
  Rank : Type w
  /-- The strict order. -/
  lt : Rank → Rank → Prop
  /-- No infinite descent. -/
  wellFounded : WellFounded lt
  /-- The measure itself. -/
  rank : p.State → Rank

namespace ProcessMeasure

variable {p : ProcessSpec.{u, w}}

/-- The measure decreases across this state change. -/
def Decreases (measure : ProcessMeasure p) (before after : p.State) : Prop :=
  measure.lt (measure.rank after) (measure.rank before)

end ProcessMeasure

/--
An event is deliverable to a process holding `outstanding` when it settles
nothing, or settles a demand that is actually outstanding.

On its own this is a weak condition — for any event, *some* bag makes it
deliverable. It is a real restriction only because `MeetsProcessProgress` pairs
it with a reachable run state, which fixes the bag.
-/
def EventDeliverable {p : ProcessSpec.{u, w}} (outstanding : Bag p.Demand)
    (event : p.Event) : Prop :=
  ∀ demand, event.settles = some demand → demand ∈ outstanding

theorem eventDeliverable_of_settles_none {p : ProcessSpec.{u, w}}
    {outstanding : Bag p.Demand} {event : p.Event}
    (settlesNothing : event.settles = none) :
    EventDeliverable outstanding event := by
  intro demand settles
  exact absurd (settlesNothing ▸ settles) (by simp)

/--
The §7 progress condition, for one transition.

Four disjuncts where §7 lists three, because §7's first one is two: "reach a
law-bearing **external/demand-result** frontier in finite internal work".

An earlier version had only the external half, and the demand-result half is not
cosmetic — a `.result` or `.interrupted` step consumes an outstanding occurrence
and may leave `p.State` untouched, which is real progress that
`ProcessMeasure.rank : p.State → Rank` structurally cannot see, because the
outstanding bag lives in `ProcessRunState` and not in the state.

**`issued.card = 0` is that disjunct's whole content**, and the first version of
it did not have the condition. Without it the disjunct fires on the event's label
alone: a step that consumes an occurrence and *reissues* one leaves the state, the
bag and the trace bit-for-bit identical and was "progress" forever. Local
adversarial review built that process — one demand, one step, an empty
`ExternalEvent` so it could not fall back on the entropy escape — and gave it a
full `ProcessCorrect` and a `MeetsProcessProgress` with a constant measure. The
condition says what the disjunct was always meant to say: an occurrence left the
outstanding bag and nothing took its place, so the bag is strictly smaller, which
is a descent the state rank cannot see and this can. `reissuing_step_decreases`
is the exported form and `Tests/Process/SpinFixtures.lean` is the witness.

`issued` is the transition's own output rather than the run's bag, which is why
this is statable here at all — `StepProgresses` is a per-step predicate and has
no run state. That is also its limit: see the module note for the two-demand
cycle it does not exclude.

See the module note for why the first disjunct is environment entropy rather
than "settled nothing"; that argument is about `.fault` and
`.environmentViolation`, and it is unaffected.
-/
def StepProgresses {p : ProcessSpec.{u, w}} (accept : ProcessAcceptance p)
    (measure : ProcessMeasure p) (before after : p.State) (event : p.Event)
    (issued : Bag p.Demand) (emitted : p.Segment) : Prop :=
  (∃ entropy, event.externalEntropy = some entropy) ∨
    (∃ demand, event.settles = some demand ∧ issued.card = 0) ∨
    accept.SegmentIsDemanded emitted ∨
    measure.Decreases before after

/--
A process meets its progress contract.

**All three fields are quantified over reachable run states**, because a claim
about a state and an outstanding bag that no execution reaches together is
neither needed nor provable. The two responsiveness fields were moved there
first; `productive` followed, and the reason is the same one in the other
direction.

`productive` used to quantify over every step from an invariant-satisfying
state. An `Invariant : p.State → Prop` sees the state and not the bag, so it
cannot say "this demand is never outstanding" — and a process is then obliged to
prove progress for results to demands it never issues. `countdown`'s `.result
.log` case is exactly that step: it answers a demand that is never in the bag,
leaves the state alone and reissues, so it progresses under no measure at all.
The first response to that was to widen `StepProgresses` until the unreachable
step passed, which let a genuinely spinning process through; see that
definition's docstring. The right response was to stop asking about it.

`Invariant` is kept beside the reachability hypothesis rather than replaced by
it. Reachability is about the run and cannot be strengthened by the caller;
`Invariant` is the caller's own, and a process whose measure descends only under
a state predicate it separately maintains needs somewhere to say so.
-/
structure MeetsProcessProgress (p : ProcessSpec.{u, w})
    (accept : ProcessAcceptance p) (Invariant : p.State → Prop)
    (request : p.Request) : Type (max (u + 1) (w + 1)) where
  /-- The internal measure. -/
  measure : ProcessMeasure p
  /--
  Every deliverable event has a successor, at every reachable state the process
  has not finished at.

  This is `docs/FOUNDATION.md` law 5 made checkable: an author cannot handle the
  results they expect and leave the rest, because every event that could arrive
  while the process is still working must have a transition.

  The non-terminality guard is not a weakening; without it this record is
  uninhabitable. See the module note.
  -/
  handlesEveryEvent : ∀ (segmented : Segmented p.Observation) (state : p.State)
      (outstanding : Bag p.Demand) (observations : Trace p.Observation)
      (event : p.Event),
    Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations) →
    ¬ (∃ result, p.Terminal request state result) →
    EventDeliverable outstanding event →
    ∃ after issued emitted, p.Step state event after issued emitted
  /--
  No reachable running state is stuck: it can terminate, or some deliverable
  event moves it.

  The terminal disjunct demands the classification, not just `p.Terminal`; see
  the module note for the hole that closes.
  -/
  notStuck : ∀ (segmented : Segmented p.Observation) (state : p.State)
      (outstanding : Bag p.Demand) (observations : Trace p.Observation),
    Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations) →
    (∃ result, p.Terminal request state result ∧
      Nonempty (TerminalDemandClassification accept.terminalRemainder request state
        result outstanding)) ∨
    (∃ event, EventDeliverable outstanding event ∧
      ∃ after issued emitted, p.Step state event after issued emitted)
  /--
  Every step a run can actually take progresses.

  Reachability and deliverability together are what make this an obligation
  about the process rather than about its type signature. See the structure's
  docstring.
  -/
  productive : ∀ (segmented : Segmented p.Observation) (state : p.State)
      (outstanding : Bag p.Demand) (observations : Trace p.Observation)
      (after : p.State) (event : p.Event)
      (issued : Bag p.Demand) (emitted : p.Segment),
    Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations) →
    Invariant state →
    EventDeliverable outstanding event →
    p.Step state event after issued emitted →
    StepProgresses accept measure state after event issued emitted

namespace MeetsProcessProgress

variable {p : ProcessSpec.{u, w}} {accept : ProcessAcceptance p}
  {Invariant : p.State → Prop} {request : p.Request}

/--
**No reachable running state is stuck.** Every one has an outgoing transition.

This is the theorem the two responsiveness fields exist for, and it is what
makes them more than a restatement. Given a reachable running state, `notStuck`
supplies either a permitted terminal disposition — which builds
`ProcessRunTransition.terminate` — or a deliverable event with a successor,
which builds `step` or `settle` according to whether the event settles a demand.
The `settle` case needs the consumed occurrence to actually be in the bag, and
that is exactly what `EventDeliverable` provides.
-/
theorem exists_transition (progress : MeetsProcessProgress p accept Invariant request)
    {segmented : Segmented p.Observation} {state : p.State}
    {outstanding : Bag p.Demand} {observations : Trace p.Observation}
    (reached : Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations)) :
    ∃ after, ProcessRunTransition accept.terminalRemainder request
      (.running state outstanding observations) after := by
  rcases progress.notStuck segmented state outstanding observations reached with
    ⟨result, isTerminal, ⟨classification⟩⟩ |
      ⟨event, deliverable, after, issued, emitted, stepped⟩
  · exact ⟨_, .terminate isTerminal classification⟩
  · match settlesCase : event.settles with
    | none => exact ⟨_, .step settlesCase stepped⟩
    | some demand =>
      obtain ⟨remainder, consume⟩ :=
        Bag.consume_iff_mem.mpr (deliverable demand settlesCase)
      exact ⟨_, .settle settlesCase consume stepped⟩

/--
A step that is not environment entropy, settles nothing, and emits nothing
demanded must decrease the measure.

The contrapositive that makes `StepProgresses` bite, and the form a livelock
argument uses: if the program's own activity comes back and nothing the
specification asked for was produced, the state got strictly smaller, and by
well-foundedness that cannot go on forever.

The `settlesNothing` hypothesis is named in the headline because a hover shows
only the first sentence and an earlier version of that sentence omitted it. It
covers faults and environment violations — which is the point of the change from
`settles` to `externalEntropy` in the *first* disjunct. For the settling case see
`reissuing_step_decreases`, which needs only the weaker hypothesis that the step
reissued something.
-/
theorem silent_nonentropy_step_decreases
    (progress : MeetsProcessProgress p accept Invariant request)
    {segmented : Segmented p.Observation} {state after : p.State}
    {outstanding : Bag p.Demand} {observations : Trace p.Observation}
    {event : p.Event} {issued : Bag p.Demand} {emitted : p.Segment}
    (reached : Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations))
    (invariant : Invariant state)
    (transition : p.Step state event after issued emitted)
    (notEntropy : event.externalEntropy = none)
    (settlesNothing : event.settles = none)
    (silent : ¬ accept.SegmentIsDemanded emitted) :
    progress.measure.Decreases state after := by
  rcases progress.productive segmented state outstanding observations after event issued
    emitted reached invariant (eventDeliverable_of_settles_none settlesNothing)
    transition with
    ⟨_, isEntropy⟩ | ⟨_, settles, _⟩ | demanded | decreases
  · exact absurd (notEntropy ▸ isEntropy) (by simp)
  · exact absurd (settlesNothing ▸ settles) (by simp)
  · exact absurd demanded silent
  · exact decreases

/--
**And a transition for the event you were handed**, not merely for some event.

`exists_transition` above uses `notStuck` alone, so `handlesEveryEvent` — the
field documented as "law 5 made checkable" — was consumed by nothing. Local
adversarial review found that and observed the fix is four lines: the same
`settles` case split, over the successor `handlesEveryEvent` supplies.

The difference matters to a driver. `exists_transition` says a reachable run can
continue; this says it can continue *with the result that just arrived*, which
is what `docs/FOUNDATION.md` law 5 is about — an admitted result being handled
rather than some other transition being available instead.

The non-terminality hypothesis is `handlesEveryEvent`'s own and cannot be
dropped: at a terminal state `ProcessCorrect.terminalNoStep` forbids the step,
and the obligation there is to terminate, which is `exists_transition`'s left
branch.
-/
theorem transition_for_event (progress : MeetsProcessProgress p accept Invariant request)
    {segmented : Segmented p.Observation} {state : p.State}
    {outstanding : Bag p.Demand} {observations : Trace p.Observation} {event : p.Event}
    (reached : Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations))
    (notTerminal : ¬ (∃ result, p.Terminal request state result))
    (deliverable : EventDeliverable outstanding event) :
    ∃ after, ProcessRunTransition accept.terminalRemainder request
      (.running state outstanding observations) after := by
  obtain ⟨after, issued, emitted, stepped⟩ :=
    progress.handlesEveryEvent segmented state outstanding observations event reached
      notTerminal deliverable
  match settlesCase : event.settles with
  | none => exact ⟨_, .step settlesCase stepped⟩
  | some demand =>
    obtain ⟨remainder, consume⟩ :=
      Bag.consume_iff_mem.mpr (deliverable demand settlesCase)
    exact ⟨_, .settle settlesCase consume stepped⟩

/--
**A step that answers a demand and issues another does not progress for free.**

The theorem that excludes a demand-reissuing spin, and the reason
`StepProgresses`'s second disjunct carries `issued.card = 0`. Consuming one
occurrence and putting another in its place leaves the outstanding bag the same
size; if the step is not entropy and emits nothing demanded, the state rank is all
that is left, and it must descend.

Note what is *not* required: the reissued demand need not be the one that was
answered. A cycle through two demands is excluded one step at a time by this
theorem and not excluded as a cycle — see the module note.
-/
theorem reissuing_step_decreases
    (progress : MeetsProcessProgress p accept Invariant request)
    {segmented : Segmented p.Observation} {state after : p.State}
    {outstanding : Bag p.Demand} {observations : Trace p.Observation}
    {event : p.Event} {issued : Bag p.Demand} {emitted : p.Segment}
    (reached : Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations))
    (invariant : Invariant state)
    (deliverable : EventDeliverable outstanding event)
    (transition : p.Step state event after issued emitted)
    (notEntropy : event.externalEntropy = none)
    (reissues : issued.card ≠ 0)
    (silent : ¬ accept.SegmentIsDemanded emitted) :
    progress.measure.Decreases state after := by
  rcases progress.productive segmented state outstanding observations after event issued
    emitted reached invariant deliverable transition with
    ⟨_, isEntropy⟩ | ⟨_, _, noneIssued⟩ | demanded | decreases
  · exact absurd (notEntropy ▸ isEntropy) (by simp)
  · exact absurd noneIssued reissues
  · exact absurd demanded silent
  · exact decreases

/--
A silent fault does not progress for free.

The specific case the earlier `settles`-based definition let through, kept as a
named corollary so a reviewer can check it directly.
-/
theorem silent_fault_decreases
    (progress : MeetsProcessProgress p accept Invariant request)
    {segmented : Segmented p.Observation} {state after : p.State}
    {outstanding : Bag p.Demand} {observations : Trace p.Observation}
    {fault : p.LogicalFault} {issued : Bag p.Demand} {emitted : p.Segment}
    (reached : Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations))
    (invariant : Invariant state)
    (transition : p.Step state (.fault fault) after issued emitted)
    (silent : ¬ accept.SegmentIsDemanded emitted) :
    progress.measure.Decreases state after :=
  progress.silent_nonentropy_step_decreases reached invariant transition
    (by simp) (by simp) silent

/--
There is no infinite silent descent.

The accessibility of the measure's rank at a state is what a coinductive
argument over maximal executions consumes at M4. Stating it here keeps the
well-foundedness obligation next to the definition that needs it.
-/
theorem accessible (progress : MeetsProcessProgress p accept Invariant request)
    (state : p.State) : Acc progress.measure.lt (progress.measure.rank state) :=
  progress.measure.wellFounded.apply _

end MeetsProcessProgress

end Grass.Process
