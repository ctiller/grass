import Grass.Process.Bag
import Grass.Process.Observation
import Grass.Process.Vocabulary

/-!
# The process specification

`docs/PROCESS.md` §2. A `ProcessSpec` is a relational state machine over the
event family of `Grass/Process/Vocabulary.lean`. It is relational rather than
functional so that nondeterministic specifications are first class, and
`DeterministicProcess` below is the convenience constructor the document asks
for, not a second semantics.

## What is deliberately absent

`docs/FOUNDATION.md` law 18 is enforced here by omission. `Step` receives a
state and an event and relates them to a new state, a demand *bag*, and an
observation segment. There is no occurrence identity, no ordering among issued
demands, no dependency edge, no routing target, no worker, and no pending
handle. A specification that wants a later demand to depend on an earlier
result expresses it as state: `docs/PROCESS.md` §2 says "a later demand is not
enabled until the transition which accepts the prerequisite result".

## The one added field

`TerminalDisposition` is not in the normative declaration. It is here because
§2 requires that on termination the run "explicitly resolves, transfers, or
permits pending for every remainder **according to the specification's
progress/lifecycle law**", and the declaration as written contains no field in
which that law could live. Without it, `ClassifiesEveryOutstandingDemand` in
`Grass/Process/Run.lean` would be an assignment with no acceptance criterion —
a function every terminal transition could satisfy by mapping everything to
`permittedPending`, which is precisely the disappearance `docs/FOUNDATION.md`
law 7 forbids.

`docs/PROCESS_IMPLEMENTATION_PLAN.md` records this as a deviation needing a
`docs/DECISIONS.md` entry. It strengthens rather than weakens: a specification
that genuinely permits anything writes `fun _ _ _ _ _ => True` and a reviewer
can see that it did.
-/

namespace Grass.Process

universe u

/--
The optional pure projection from process state to a desired view.

`docs/PROCESS.md` §2: "An optional view facet is pure. It may be evaluated,
duplicated, coalesced, or discarded without changing platform resources or
producing an observation." That is why `render` is a function into a plain type
and not a relation into demands: a view that could emit is not a view.
-/
structure ViewFacet (State : Type u) : Type (u + 1) where
  /-- The desired-state type this process projects. -/
  View : Type u
  /-- The projection. Total and pure. -/
  render : State → View

/--
What a terminal transition says about a demand still outstanding when the
process ends.

`docs/PROCESS.md` §2 names exactly these three: a terminal transition
"explicitly resolves, transfers, or permits pending for every remainder".

The third is not a loophole. `permittedPending` is a *claim* that the
specification tolerates this interaction never being answered — for instance a
best-effort log write abandoned at shutdown — and `ProcessSpec.TerminalDisposition`
is where the specification has to have said so.
-/
inductive TerminalDemandDisposition
  /-- The demand was answered, or its effect is known to have completed. -/
  | resolved
  /-- Custody of the interaction passed to another process or to the driver. -/
  | transferred
  /-- The specification permits this interaction to remain unanswered forever. -/
  | permittedPending
  deriving DecidableEq, Repr

/--
One process: its interface, its state, and its relational behavior.

Extends `ProcessVocabulary`, so a `ProcessSpec` is a vocabulary plus a machine
over it, and a child protocol registry can hold either.
-/
structure ProcessSpec : Type (u + 1) extends ProcessVocabulary.{u} where
  /-- The parameter this process is started with. -/
  Request : Type u
  /-- Private local state. Not visible to a parent; see `docs/PROCESS.md` §3. -/
  State : Type u
  /-- The typed value a terminal transition produces. -/
  TerminalResult : Type u
  /--
  The permitted initial configurations for a request: a state, the demands
  issued before any event arrives, and the observations emitted by starting.
  -/
  Initial : Request → State → Bag Demand → ObservationSegment Observation → Prop
  /-- The states at which this request may finish, and with what result. -/
  Terminal : Request → State → TerminalResult → Prop
  /--
  The transition relation: from a state, on an event, to a state, the demands
  this transition issues, and the observations it emits.

  The bag and the segment are the output of *this* transition only. Outstanding
  demands and the accumulated trace live in the run, not in `State`.
  -/
  Step : State → ProcessEvent toProcessVocabulary → State → Bag Demand →
    ObservationSegment Observation → Prop
  /--
  Which dispositions this specification permits for a demand still outstanding
  at a terminal state. See the module note for why this field exists.
  -/
  TerminalDisposition :
    Request → State → TerminalResult → Demand → TerminalDemandDisposition → Prop
  /--
  The desired-view projection, when the process has one.

  `none` is the normal choice. `docs/PROCESS.md` §2: "`view := none` is the
  normal choice for filters, servers, API calls, and other processes with no
  pure desired-state projection."
  -/
  view : Option (ViewFacet State)

namespace ProcessSpec

variable (p : ProcessSpec.{u})

/-- The event family of this process. -/
abbrev Event := ProcessEvent p.toProcessVocabulary

/-- The demand multiset type of this process. -/
abbrev Demands := Bag p.Demand

/-- The observation segment type of this process. -/
abbrev Segment := ObservationSegment p.Observation

end ProcessSpec

/--
The deterministic authoring convenience of `docs/PROCESS.md` §2.

`initial`, `terminal`, and `update` are functions; `toProcessSpec` derives the
relations. This is a constructor, not a second semantics: everything downstream
consumes the derived `ProcessSpec`, and `deterministic_step_functional` below is
the only extra fact it buys.
-/
structure DeterministicProcess (v : ProcessVocabulary.{u}) : Type (u + 1) where
  /-- The parameter this process is started with. -/
  Request : Type u
  /-- Private local state. -/
  State : Type u
  /-- The typed value produced on termination. -/
  TerminalResult : Type u
  /-- The unique initial configuration for a request. -/
  initial : Request → State × Bag v.Demand × ObservationSegment v.Observation
  /-- Whether this state is terminal for this request, and with what result. -/
  terminal : Request → State → Option TerminalResult
  /-- The unique successor configuration for a state and event. -/
  update : State → ProcessEvent v →
    State × Bag v.Demand × ObservationSegment v.Observation
  /-- Which terminal dispositions the specification permits. -/
  terminalDisposition :
    Request → State → TerminalResult → v.Demand → TerminalDemandDisposition → Prop
  /-- The desired-view projection, when there is one. -/
  view : Option (ViewFacet State)

namespace DeterministicProcess

variable {v : ProcessVocabulary.{u}} (d : DeterministicProcess v)

/-- The relational process this deterministic description denotes. -/
def toProcessSpec : ProcessSpec.{u} where
  toProcessVocabulary := v
  Request := d.Request
  State := d.State
  TerminalResult := d.TerminalResult
  Initial := fun request state issued emitted =>
    d.initial request = (state, issued, emitted)
  Terminal := fun request state result => d.terminal request state = some result
  Step := fun state event after issued emitted =>
    d.update state event = (after, issued, emitted)
  TerminalDisposition := d.terminalDisposition
  view := d.view

@[simp] theorem toProcessSpec_toProcessVocabulary :
    d.toProcessSpec.toProcessVocabulary = v := rfl

@[simp] theorem toProcessSpec_Initial (request : d.Request) (state : d.State)
    (issued : Bag v.Demand) (emitted : ObservationSegment v.Observation) :
    d.toProcessSpec.Initial request state issued emitted ↔
      d.initial request = (state, issued, emitted) := Iff.rfl

@[simp] theorem toProcessSpec_Step (state : d.State) (event : ProcessEvent v)
    (after : d.State) (issued : Bag v.Demand)
    (emitted : ObservationSegment v.Observation) :
    d.toProcessSpec.Step state event after issued emitted ↔
      d.update state event = (after, issued, emitted) := Iff.rfl

/--
The derived relation is functional: a state and an event have at most one
successor, one issued bag, and one segment.

This is what an author gets for choosing the deterministic constructor, and it
is also the honest statement of what they gave up. `docs/SEMANTICS.md`'s
nondeterminism is not weakened by the existence of this constructor, because a
process that needs to admit several successors simply does not use it.
-/
theorem step_functional {state : d.State} {event : ProcessEvent v}
    {afterLeft afterRight : d.State}
    {issuedLeft issuedRight : Bag v.Demand}
    {emittedLeft emittedRight : ObservationSegment v.Observation}
    (left : d.toProcessSpec.Step state event afterLeft issuedLeft emittedLeft)
    (right : d.toProcessSpec.Step state event afterRight issuedRight emittedRight) :
    afterLeft = afterRight ∧ issuedLeft = issuedRight ∧
      emittedLeft = emittedRight := by
  have equal : (afterLeft, issuedLeft, emittedLeft) =
      (afterRight, issuedRight, emittedRight) := left ▸ right
  exact ⟨congrArg (·.1) equal, congrArg (·.2.1) equal, congrArg (·.2.2) equal⟩

/-- The derived initial relation is functional, for the same reason. -/
theorem initial_functional {request : d.Request}
    {stateLeft stateRight : d.State}
    {issuedLeft issuedRight : Bag v.Demand}
    {emittedLeft emittedRight : ObservationSegment v.Observation}
    (left : d.toProcessSpec.Initial request stateLeft issuedLeft emittedLeft)
    (right : d.toProcessSpec.Initial request stateRight issuedRight emittedRight) :
    stateLeft = stateRight ∧ issuedLeft = issuedRight ∧
      emittedLeft = emittedRight := by
  have equal : (stateLeft, issuedLeft, emittedLeft) =
      (stateRight, issuedRight, emittedRight) := left ▸ right
  exact ⟨congrArg (·.1) equal, congrArg (·.2.1) equal, congrArg (·.2.2) equal⟩

/-- The derived terminal relation is functional in the result. -/
theorem terminal_functional {request : d.Request} {state : d.State}
    {left right : d.TerminalResult}
    (leftTerminal : d.toProcessSpec.Terminal request state left)
    (rightTerminal : d.toProcessSpec.Terminal request state right) :
    left = right :=
  Option.some.inj (leftTerminal ▸ rightTerminal)

end DeterministicProcess

end Grass.Process
