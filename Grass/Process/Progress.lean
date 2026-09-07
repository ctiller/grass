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

## Reading the three disjuncts at this layer

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

So `StepProgresses` is: environment entropy arrived, **or** the transition
emitted an observation the specification demanded, **or** a well-founded measure
strictly decreased. A server's accept loop satisfies the second disjunct on every
connection. A silent fault loop satisfies none.

**Where the demand-result half of §7's first clause went.** It reads as though
answering a demand is progress on its own, and two drafts made it a disjunct of
its own. The first fired on the event's label, so a process that answers a demand
and reissues it forever was correct — `Tests/Process/SpinFixtures.lean`. The
second required the step to issue nothing, which excludes that one and creates a
worse problem: a disjunct about the bag and a disjunct about a state rank are
*two independent well-founded orders*, and a disjunction of two orders is not an
order. `Tests/Process/OscillateFixtures.lean` alternates between them, descending
in each on alternate steps, and returns the run state bit-for-bit — with a full
`ProcessCorrect`.

It is now inside the measure. `ProcessMeasure.rank` takes the outstanding bag
beside the state, so "an occurrence left and nothing replaced it" is something an
author's own rank can see, and cannot be traded against a rank that climbs back.
Both fixtures are kept, because neither is excluded by pinning the other.

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
`p.Terminal` for every request. An unguarded `handlesEveryEvent` demands a
`p.Step` at every reachable running state — and the running state a terminating
run fires `terminate` from is reachable and terminal. The two fields contradicted
each other, and no process with such a state had a `ProcessCorrect` at all.

The class that suffers is narrower than an earlier version of this paragraph
said. It is processes with a reachable running state terminal for *every*
request — `oneShot`, `countdown` and `hiccup`. A process whose `Terminal` depends
on the request has no such state: `Tests/Process/PrefixFixtures.lean`'s `upto`
inhabits the *unguarded* record perfectly well, which a reviewer checked by
building it. So the guard is a genuine weakening for the request-dependent class
and a necessity for the other, and no fixture separates those two facts; §10.45's
proposal to index `p.Step` by the request is what would make the guard
unnecessary for both.

Law 5 applies where the process is still working; at a terminal state the
obligation is to terminate, which is `notStuck`'s left disjunct.

## What this layer still cannot exclude

The module note above records that "waiting forever for entropy that never
comes" passes, because nothing here declares which frontiers are law-bearing.
The dual passes too, and is worth naming: `ExternalEvent` is chosen by the
specification author, so a process can route its own internal work through a
self-delivered tick, satisfy the entropy disjunct forever, never terminate,
never emit, and never decrease its measure. A total livelock of that shape has a
`ProcessCorrect`.

`countdown`, this corpus's own positive fixture, is an instance: its
`.external .wake` at a non-zero state returns the run state unchanged and is
discharged by the entropy disjunct. So the corpus contains a livelock presented
as the witness and two presented as the excluded ones, and what separates them is
exactly this: `countdown` calls its loop external and `spin` and `osc` have no
external events to call it.

**And the third disjunct has the same shape**, which a reviewer showed by
building `Tests/Process/ChatterFixtures.lean`: a process with no external events
at all, faulting forever and emitting one demanded observation each time, has a
full `ProcessCorrect`. `ProcessAcceptance.Demanded`'s own docstring says the
field exists so that "every process could satisfy progress by logging" is false,
and that is what `chatter` does — with a logged value the specification demands.

The pattern across all of them is worth naming. Every livelock this corpus knows
about escapes through a predicate the *specification's author* supplies —
`ExternalEvent` or `Demanded` — and none escapes through the measure. That the
measure is now airtight took `Tests/Process/SpinFixtures.lean` and
`Tests/Process/OscillateFixtures.lean` and two rounds; that the two predicates
are not is `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.70.

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
A well-founded internal measure on **a running process**: its state and the
demands it is waiting on.

`Rank` is a type rather than `Nat` because a lexicographic or structural measure
is normal for a state machine with phases, and forcing it through `Nat` costs an
encoding proof for nothing.

## Why the bag is an argument

`docs/PROCESS.md` §2's `ProcessRunState.running` carries `outstanding` beside
the local state, and a process that answers one of its own demands has made
progress even if `p.State` is untouched. A rank over `p.State` alone cannot see
that, and the first repair for it was a *separate disjunct* in `StepProgresses`
saying "a demand was answered and none reissued".

**That was wrong, and it took three attempts to see why.** Two independent
descent orders in a disjunction do not compose into one: a process can descend
in the bag on one step, descend in the state on the next, and return to exactly
where it started. Local adversarial review built it — `osc` in
`Tests/Process/OscillateFixtures.lean` answers its demand and issues *two* while
the state rank falls, then answers and issues *none* while the rank climbs back
— and gave it a full `ProcessCorrect` with a two-step cycle returning the run
state bit-for-bit. Neither the bag nor the rank is constant along that cycle,
which is why the "cardinality is constant" diagnosis recorded at the time was
also wrong.

One rank over both components is the repair, and it costs an author nothing they
were not already choosing: a measure that ignores the bag is `fun state _ => …`,
and a measure that is only about the bag is `fun _ bag => bag.card`.
-/
structure ProcessMeasure (p : ProcessSpec.{u, w}) : Type (max (u + 1) (w + 1)) where
  /-- The ordered carrier. -/
  Rank : Type w
  /-- The strict order. -/
  lt : Rank → Rank → Prop
  /-- No infinite descent. -/
  wellFounded : WellFounded lt
  /-- The measure itself, over the state and the demands outstanding at it. -/
  rank : p.State → Bag p.Demand → Rank

namespace ProcessMeasure

variable {p : ProcessSpec.{u, w}}

/-- The measure decreases across this run step. -/
def Decreases (measure : ProcessMeasure p) (before : p.State)
    (beforeOutstanding : Bag p.Demand) (after : p.State)
    (afterOutstanding : Bag p.Demand) : Prop :=
  measure.lt (measure.rank after afterOutstanding) (measure.rank before beforeOutstanding)

/--
**A run cannot get smaller both ways.**

A well-founded order is asymmetric, so a measure cannot certify progress from one
running configuration to another *and* back. This is the fact one rank over
`(state, outstanding)` buys and two ranks in a disjunction do not:
`Tests/Process/OscillateFixtures.lean` is the process that descended in the bag
one step and in the state rank the next, and returned the run to where it
started.
-/
theorem not_decreases_both_ways (measure : ProcessMeasure p)
    {before after : p.State} {beforeOutstanding afterOutstanding : Bag p.Demand}
    (there : measure.Decreases before beforeOutstanding after afterOutstanding)
    (back : measure.Decreases after afterOutstanding before beforeOutstanding) : False := by
  have asymmetric : ∀ left, ∀ right, measure.lt left right → measure.lt right left → False := by
    intro left
    have acc : Acc measure.lt left := measure.wellFounded.apply left
    induction acc with
    | intro _ _ ih => exact fun right leftLt rightLt => ih right rightLt _ rightLt leftLt
  exact asymmetric _ _ back there

/-- And in particular a step that changes neither the state nor the bag never
decreases the measure. -/
theorem not_decreases_self (measure : ProcessMeasure p) (state : p.State)
    (outstanding : Bag p.Demand) :
    ¬ measure.Decreases state outstanding state outstanding :=
  fun self => measure.not_decreases_both_ways self self

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

/--
The bag a run holds after this step.

`Grass/Process/Run.lean`'s two stepping constructors, as a predicate: a
non-settling event adds what was issued, and a settling one consumes exactly one
matching occurrence first. Stating it here rather than reading it off a
`ProcessRunTransition` is what lets `MeetsProcessProgress.productive` be about a
step without being about a constructor.

It implies `EventDeliverable` — see below — so a `productive` obligation stated
over it does not need deliverability as a separate hypothesis.
-/
def SuccessorBag {p : ProcessSpec.{u, w}} (outstanding : Bag p.Demand) (event : p.Event)
    (issued afterOutstanding : Bag p.Demand) : Prop :=
  match event.settles with
  | none => afterOutstanding = outstanding + issued
  | some demand => ∃ remainder, Bag.ConsumeExactlyOneMatching outstanding demand remainder ∧
      afterOutstanding = remainder + issued

/-- A successor bag exists only for an event the process could be handed. -/
theorem eventDeliverable_of_successorBag {p : ProcessSpec.{u, w}}
    {outstanding : Bag p.Demand} {event : p.Event} {issued afterOutstanding : Bag p.Demand}
    (successor : SuccessorBag outstanding event issued afterOutstanding) :
    EventDeliverable outstanding event := by
  intro demand settles
  unfold SuccessorBag at successor
  rw [settles] at successor
  obtain ⟨_, consume, _⟩ := successor
  exact consume.mem

/-- And a non-settling event's successor bag is the one `Run.lean` builds. -/
theorem successorBag_of_settles_none {p : ProcessSpec.{u, w}}
    {outstanding : Bag p.Demand} {event : p.Event} {issued : Bag p.Demand}
    (settlesNothing : event.settles = none) :
    SuccessorBag outstanding event issued (outstanding + issued) := by
  unfold SuccessorBag
  rw [settlesNothing]

theorem eventDeliverable_of_settles_none {p : ProcessSpec.{u, w}}
    {outstanding : Bag p.Demand} {event : p.Event}
    (settlesNothing : event.settles = none) :
    EventDeliverable outstanding event := by
  intro demand settles
  exact absurd (settlesNothing ▸ settles) (by simp)

/--
The §7 progress condition, for one transition.

Three disjuncts, which is what §7 lists.

§7's first clause is "reach a law-bearing **external/demand-result** frontier in
finite internal work", and it is tempting to read the two halves as two
disjuncts. Two drafts did, and both were wrong.

The first fired on the event's label alone: a step that answers a demand and
*reissues* one leaves the state, the bag and the trace bit-for-bit identical, and
was progress forever. `Tests/Process/SpinFixtures.lean` is that process.

The second added `issued.card = 0`, which excludes it — and introduced a subtler
failure that survived a whole review round. A demand-result disjunct and a
measure disjunct are **two independent descent orders**, and a disjunction of two
orders is not an order: a process can descend in the bag on one step, descend in
the state rank on the next, and be back where it started.
`Tests/Process/OscillateFixtures.lean` is that process, and it had a full
`ProcessCorrect`.

The demand-result half is now inside the measure, which takes the outstanding bag
as an argument — see `ProcessMeasure`. A step that answers a demand and issues
nothing shrinks the bag, and an author who wants that to count says so by ranking
the bag. What they cannot do is have it counted *and* have the rank climb back.

See the module note for why the first disjunct is environment entropy rather
than "settled nothing"; that argument is about `.fault` and
`.environmentViolation`, and it is unaffected.
-/
def StepProgresses {p : ProcessSpec.{u, w}} (accept : ProcessAcceptance p)
    (measure : ProcessMeasure p) (before : p.State) (beforeOutstanding : Bag p.Demand)
    (after : p.State) (afterOutstanding : Bag p.Demand)
    (event : p.Event) (emitted : p.Segment) : Prop :=
  (∃ entropy, event.externalEntropy = some entropy) ∨
    accept.SegmentIsDemanded emitted ∨
    measure.Decreases before beforeOutstanding after afterOutstanding

/--
A process meets its progress contract.

**All three fields are quantified over reachable run states**, because a claim
about a state and an outstanding bag that no execution reaches together is not
needed. The two responsiveness fields were moved there first; `productive`
followed, and the reason is the same one in the other direction.

It is not that such a claim is *unprovable* — an earlier version of this
paragraph said so and a reviewer refuted it in one file, by discharging
`handlesEveryEvent` for `upto` with no reachability hypothesis at all. It is that
requiring it costs a correct process its record, which is what happened to
`countdown`.

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

  The non-terminality guard is a weakening for some processes and a necessity
  for others, and the module note says which. It is *not* true that the record
  is uninhabitable without it — `Tests/Process/PrefixFixtures.lean`'s `upto`
  terminates and satisfies the unguarded field, which a reviewer checked by
  building it. What is true is that `oneShot`, `countdown` and `hiccup` do not,
  because each has a reachable running state terminal for every request, where
  `ProcessCorrect.terminalNoStep` forbids the step this field would demand.
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
      (after : p.State) (afterOutstanding : Bag p.Demand) (event : p.Event)
      (issued : Bag p.Demand) (emitted : p.Segment),
    Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations) →
    Invariant state →
    SuccessorBag outstanding event issued afterOutstanding →
    p.Step state event after issued emitted →
    StepProgresses accept measure state outstanding after afterOutstanding event emitted

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
A step that is not environment entropy and emits nothing demanded must decrease
the measure.

The contrapositive that makes `StepProgresses` bite, and the form a livelock
argument uses: if the program's own activity comes back and nothing the
specification asked for was produced, the run got strictly smaller, and by
well-foundedness that cannot go on forever.

Two hypotheses an earlier version needed are gone, and both were symptoms of the
demand-result disjunct. It required the step to settle nothing, so it said nothing
about `.result` or `.interrupted`; and there was a second theorem for those.
Folding the outstanding bag into the measure left one theorem covering every
non-entropy event, which is what §7's three-way reading is.
-/
theorem silent_nonentropy_step_decreases
    (progress : MeetsProcessProgress p accept Invariant request)
    {segmented : Segmented p.Observation} {state after : p.State}
    {outstanding afterOutstanding : Bag p.Demand} {observations : Trace p.Observation}
    {event : p.Event} {issued : Bag p.Demand} {emitted : p.Segment}
    (reached : Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations))
    (invariant : Invariant state)
    (successor : SuccessorBag outstanding event issued afterOutstanding)
    (transition : p.Step state event after issued emitted)
    (notEntropy : event.externalEntropy = none)
    (silent : ¬ accept.SegmentIsDemanded emitted) :
    progress.measure.Decreases state outstanding after afterOutstanding := by
  rcases progress.productive segmented state outstanding observations after afterOutstanding
    event issued emitted reached invariant successor transition with
    ⟨_, isEntropy⟩ | demanded | decreases
  · exact absurd (notEntropy ▸ isEntropy) (by simp)
  · exact absurd demanded silent
  · exact decreases

/--
**And a transition for the event you were handed**, not merely for some event.

`exists_transition` above uses `notStuck` alone, so `handlesEveryEvent` — the
field documented as "law 5 made checkable" — was consumed by nothing.

**And the first attempt at spending it did not spend it either.** Its conclusion
was `∃ after, ProcessRunTransition … after`, which never mentions `event`, so it
is `exists_transition`'s conclusion verbatim and provable by discarding the
field, the non-terminality hypothesis and the deliverability alike. Local
adversarial review reproved it that way. A theorem is about the event it is handed
only if the event appears in what it concludes.

It does now: the successor run state is the one the step and the event determine —
the reached state, the bag `SuccessorBag` computes, and the trace extended by
exactly what the step emitted. `docs/FOUNDATION.md` law 5 is about an admitted
result being *handled*, not about some other transition being available instead,
and that is the difference between the two statements.

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
    ∃ (after : p.State) (issued emitted : _) (afterOutstanding : Bag p.Demand),
      p.Step state event after issued emitted ∧
      SuccessorBag outstanding event issued afterOutstanding ∧
      ProcessRunTransition accept.terminalRemainder request
        (.running state outstanding observations)
        (.running after afterOutstanding (observations ++ emitted)) := by
  obtain ⟨after, issued, emitted, stepped⟩ :=
    progress.handlesEveryEvent segmented state outstanding observations event reached
      notTerminal deliverable
  match settlesCase : event.settles with
  | none =>
    exact ⟨after, issued, emitted, outstanding + issued, stepped,
      successorBag_of_settles_none settlesCase, .step settlesCase stepped⟩
  | some demand =>
    obtain ⟨remainder, consume⟩ :=
      Bag.consume_iff_mem.mpr (deliverable demand settlesCase)
    refine ⟨after, issued, emitted, remainder + issued, stepped, ?_,
      .settle settlesCase consume stepped⟩
    unfold SuccessorBag
    rw [settlesCase]
    exact ⟨remainder, consume, rfl⟩

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
    progress.measure.Decreases state outstanding after (outstanding + issued) :=
  progress.silent_nonentropy_step_decreases reached invariant
    (successorBag_of_settles_none (by simp)) transition (by simp) silent

/--
The accessibility of the measure's rank at a running configuration.

What the two livelock theorems below run on, and what a coinductive argument
over maximal executions consumes at M4.
-/
theorem accessible (progress : MeetsProcessProgress p accept Invariant request)
    (state : p.State) (outstanding : Bag p.Demand) :
    Acc progress.measure.lt (progress.measure.rank state outstanding) :=
  progress.measure.wellFounded.apply _

end MeetsProcessProgress

/-! ## No silent livelock -/

/--
One silent step of a run: not environment entropy, and emitting nothing the
specification demanded.

The shape a livelock is made of. `SuccessorBag` is what makes it a step of a
*run* rather than of the transition relation alone — it carries the bag the run
holds afterwards, which is half of what the measure ranks.
-/
def SilentStep {p : ProcessSpec.{u, w}} (accept : ProcessAcceptance p)
    (before : p.State) (beforeOutstanding : Bag p.Demand)
    (after : p.State) (afterOutstanding : Bag p.Demand) : Prop :=
  ∃ (event : p.Event) (issued : Bag p.Demand) (emitted : p.Segment),
    p.Step before event after issued emitted ∧
    SuccessorBag beforeOutstanding event issued afterOutstanding ∧
    event.externalEntropy = none ∧
    ¬ accept.SegmentIsDemanded emitted

namespace MeetsProcessProgress

variable {p : ProcessSpec.{u, w}} {accept : ProcessAcceptance p}
  {Invariant : p.State → Prop} {request : p.Request}

/-- A silent step from a reachable, invariant-satisfying configuration descends
the measure. -/
theorem silent_step_descends (progress : MeetsProcessProgress p accept Invariant request)
    {segmented : Segmented p.Observation} {state after : p.State}
    {outstanding afterOutstanding : Bag p.Demand} {observations : Trace p.Observation}
    (reached : Reachable accept.terminalRemainder request segmented
      (.running state outstanding observations))
    (invariant : Invariant state)
    (silent : SilentStep accept state outstanding after afterOutstanding) :
    progress.measure.Decreases state outstanding after afterOutstanding := by
  obtain ⟨_, _, _, stepped, successor, notEntropy, undemanded⟩ := silent
  exact progress.silent_nonentropy_step_decreases reached invariant successor stepped
    notEntropy undemanded

/--
**A run cannot take two silent steps and be back where it started.**

`Tests/Process/OscillateFixtures.lean` lifted off its fixture. That process
descended the outstanding bag on one step and a state rank on the next, and
returned the run state bit-for-bit; this is the statement that no process can,
whatever its measure.

Two steps rather than one because a *one*-step silent cycle is
`ProcessMeasure.not_decreases_self`, and the two-step case is the one the
four-disjunct `StepProgresses` admitted.
-/
theorem no_silent_two_cycle (progress : MeetsProcessProgress p accept Invariant request)
    {segmentedA segmentedB : Segmented p.Observation} {stateA stateB : p.State}
    {bagA bagB : Bag p.Demand} {observationsA observationsB : Trace p.Observation}
    (reachedA : Reachable accept.terminalRemainder request segmentedA
      (.running stateA bagA observationsA))
    (reachedB : Reachable accept.terminalRemainder request segmentedB
      (.running stateB bagB observationsB))
    (invariantA : Invariant stateA) (invariantB : Invariant stateB)
    (there : SilentStep accept stateA bagA stateB bagB)
    (back : SilentStep accept stateB bagB stateA bagA) : False :=
  progress.measure.not_decreases_both_ways
    (progress.silent_step_descends reachedA invariantA there)
    (progress.silent_step_descends reachedB invariantB back)

/--
**And there is no infinite silent run at all.**

The theorem the whole module is for, and it was left to M4 for one round too
many. `docs/PROCESS.md` §7's livelock exclusion, at the per-process layer: an
execution whose every step is non-entropy and emits nothing demanded gives an
infinite descending chain in a well-founded order, which is a contradiction.

Stating it here rather than only in fixtures is what makes a future re-widening
of `StepProgresses` fail loudly. `Tests/Process/SpinFixtures.lean` and
`Tests/Process/OscillateFixtures.lean` each catch one shape; this catches every
shape, so a re-widening that admits any silent cycle at all goes red here
instead of going unnoticed until someone builds the right counterexample.

The escapes it does not close are the ones the module note discloses, and there
are four rather than three: environment entropy (an author's own choice of
`ExternalEvent`), a permissive `Demanded`, a specification with no initial state
at all, and — the one a reviewer added — a process that emits a *demanded*
observation on every step while moving neither its state nor its bag.
`Tests/Process/ChatterFixtures.lean` is that process, and it has a full
`ProcessCorrect`. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §6, §10.49, §10.55 and
§10.70.
-/
theorem no_infinite_silent_run (progress : MeetsProcessProgress p accept Invariant request)
    (states : Nat → p.State) (bags : Nat → Bag p.Demand)
    (observations : Nat → Trace p.Observation) (segmented : Nat → Segmented p.Observation)
    (reached : ∀ index, Reachable accept.terminalRemainder request (segmented index)
      (.running (states index) (bags index) (observations index)))
    (invariant : ∀ index, Invariant (states index))
    (silent : ∀ index,
      SilentStep accept (states index) (bags index) (states (index + 1)) (bags (index + 1))) :
    False := by
  have descends : ∀ index, progress.measure.lt
      (progress.measure.rank (states (index + 1)) (bags (index + 1)))
      (progress.measure.rank (states index) (bags index)) :=
    fun index =>
      progress.silent_step_descends (reached index) (invariant index) (silent index)
  have noChain : ∀ rank, ∀ index,
      progress.measure.rank (states index) (bags index) ≠ rank := by
    intro rank
    induction rank using progress.measure.wellFounded.induction with
    | _ current ih =>
      intro index isCurrent
      exact ih _ (isCurrent ▸ descends index) (index + 1) rfl
  exact noChain _ 0 rfl

end MeetsProcessProgress

end Grass.Process
