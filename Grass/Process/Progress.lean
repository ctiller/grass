import Grass.Process.Acceptance

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
sharper question: which arriving events are entropy, and which are the process's
own work coming back?

`ProcessEvent.settles` answers it. An `.external` event, a `.fault`, and an
`.environmentViolation` are entropy: the process was waiting, and waiting
forever at a declared frontier is legitimate — `docs/PROCESS.md` §7 says
"Long-lived processes need not terminate". A `.result` or `.interrupted` event
is the process's own outstanding demand coming back, and a process that issues a
demand, receives it, issues another, and never emits anything is the livelock
that a progress theorem exists to exclude.

So `StepProgresses` below is: entropy arrived, **or** the transition emitted an
observation the specification demanded, **or** a well-founded measure strictly
decreased. A server's accept loop satisfies the second disjunct on every
connection. A silent demand-issuing spin satisfies none, and is rejected.

The measure is over `p.State` because it is the process's *internal* measure.
It is not a bound on how many events arrive.

## Responsiveness is the other half

`docs/FOUNDATION.md` law 5 requires every admitted external or nondeterministic
result to be handled. A process whose `Step` relation has no successor for a
result it asked for is stuck, and stuckness is not caught by any measure — the
measure only constrains steps that happen. `Responsive` is that obligation, and
it is why `MeetsProcessProgress` has two fields rather than one.
-/

namespace Grass.Process

universe u

/--
A well-founded internal measure on process state.

`Rank` is a type rather than `Nat` because a lexicographic or structural measure
is normal for a state machine with phases, and forcing it through `Nat` costs an
encoding proof for nothing.
-/
structure ProcessMeasure (p : ProcessSpec.{u}) : Type (u + 1) where
  /-- The ordered carrier. -/
  Rank : Type u
  /-- The strict order. -/
  lt : Rank → Rank → Prop
  /-- No infinite descent. -/
  wellFounded : WellFounded lt
  /-- The measure itself. -/
  rank : p.State → Rank

namespace ProcessMeasure

variable {p : ProcessSpec.{u}}

/-- The measure decreases across this state change. -/
def Decreases (measure : ProcessMeasure p) (before after : p.State) : Prop :=
  measure.lt (measure.rank after) (measure.rank before)

end ProcessMeasure

/--
An event is deliverable to a process holding `outstanding` when it settles
nothing, or settles a demand that is actually outstanding.

This is the precondition of `Responsive`. Without it, responsiveness would
demand a successor for the completion of a demand the process never issued,
which no correct process should have.
-/
def EventDeliverable {p : ProcessSpec.{u}} (outstanding : Bag p.Demand)
    (event : p.Event) : Prop :=
  ∀ demand, event.settles = some demand → demand ∈ outstanding

theorem eventDeliverable_of_settles_none {p : ProcessSpec.{u}}
    {outstanding : Bag p.Demand} {event : p.Event}
    (settlesNothing : event.settles = none) :
    EventDeliverable outstanding event := by
  intro demand settles
  exact absurd (settlesNothing ▸ settles) (by simp)

/--
The §7 three-way progress condition, for one transition.

See the module note for why the first disjunct is `settles = none` rather than a
separate frontier predicate.
-/
def StepProgresses {p : ProcessSpec.{u}} (accept : ProcessAcceptance p)
    (measure : ProcessMeasure p) (before after : p.State) (event : p.Event)
    (emitted : p.Segment) : Prop :=
  event.settles = none ∨
    accept.SegmentIsDemanded emitted ∨
    measure.Decreases before after

/--
A process meets its progress contract.

Both fields are quantified over states satisfying an invariant supplied by the
caller, because a progress claim about unreachable states is neither needed nor
provable. `Grass/Process/Correct.lean` passes its own `Invariant`.
-/
structure MeetsProcessProgress (p : ProcessSpec.{u}) (accept : ProcessAcceptance p)
    (Invariant : p.State → Prop) (request : p.Request) : Type (u + 1) where
  /-- The internal measure. -/
  measure : ProcessMeasure p
  /--
  No stuck state: at any invariant-satisfying state, either the process may
  terminate, or every deliverable event has a successor.

  This is `docs/FOUNDATION.md` law 5 made checkable at this layer.
  -/
  responsive : ∀ (state : p.State) (outstanding : Bag p.Demand) (event : p.Event),
    Invariant state → EventDeliverable outstanding event →
    (∃ result, p.Terminal request state result) ∨
    (∃ after issued emitted, p.Step state event after issued emitted)
  /-- Every step from an invariant-satisfying state progresses. -/
  productive : ∀ (state after : p.State) (event : p.Event)
      (issued : Bag p.Demand) (emitted : p.Segment),
    Invariant state → p.Step state event after issued emitted →
    StepProgresses accept measure state after event emitted

namespace MeetsProcessProgress

variable {p : ProcessSpec.{u}} {accept : ProcessAcceptance p}
  {Invariant : p.State → Prop} {request : p.Request}

/--
A settling step that emits nothing demanded must decrease the measure.

This is the contrapositive that makes the definition bite, and it is the form a
livelock argument uses: if the process's own work comes back and nothing the
specification asked for was produced, the state got strictly smaller, and by
well-foundedness that cannot go on forever.
-/
theorem settling_silent_step_decreases
    (progress : MeetsProcessProgress p accept Invariant request)
    {state after : p.State} {event : p.Event} {demand : p.Demand}
    {issued : Bag p.Demand} {emitted : p.Segment}
    (invariant : Invariant state)
    (transition : p.Step state event after issued emitted)
    (settles : event.settles = some demand)
    (silent : ¬ accept.SegmentIsDemanded emitted) :
    progress.measure.Decreases state after := by
  rcases progress.productive state after event issued emitted invariant transition with
    settlesNothing | demanded | decreases
  · exact absurd (settlesNothing ▸ settles) (by simp)
  · exact absurd demanded silent
  · exact decreases

/--
There is no infinite silently-settling descent.

The `WellFounded.apply` accessibility of the measure's rank at the state is what
a coinductive argument over maximal executions consumes at M4. Stating it here
keeps the well-foundedness obligation next to the definition that needs it.
-/
theorem accessible (progress : MeetsProcessProgress p accept Invariant request)
    (state : p.State) : Acc progress.measure.lt (progress.measure.rank state) :=
  progress.measure.wellFounded.apply _

end MeetsProcessProgress

end Grass.Process
