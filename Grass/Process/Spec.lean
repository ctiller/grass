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

## The vocabulary is selected, not spelled

`agent-bus` disposition `g-design:4`, ruling on issue `c-process:9`:

> Per-`ProcessVocabulary` classes are ratified, but vocabulary selection belongs
> at a reusable network/protocol boundary rather than adding bespoke fields to
> every ordinary `ProcessSpec` author surface. Cross-vocabulary delivery owes a
> total classifier; an empty target class proves unreachability.

An earlier version had `ProcessSpec extends ProcessVocabulary`, which meant that
carrying the fault, interruption, and violation classes per vocabulary added
three fields to every authored specification. `g-reviewer` blocked on exactly
that, and rightly: the golden spike literals stopped elaborating.

`vocabulary` is therefore a field. An author writes one line selecting a
reusable vocabulary — `vocabulary := Http2.serverVocabulary`, or
`ProcessVocabulary.quiescent ...` for a process with no faults — and writes no
interface fields at all. That is *fewer* fields than before the fault classes
were carried, not more.

The accessors below mean no consumer noticed: `p.Demand`, `p.Observation`,
`p.Event` and the rest are what they always were.

The other half of the ruling — that cross-vocabulary delivery owes a total
classifier, so an empty class is a proof of unreachability rather than a bypass
— is an obligation on the network transition family, and is M2 work.

## Two universes, not one

The interface types — external events, demands, results, observations, and the
fault classes — live in `u`. The *private* types — request, state, terminal
result, and the view — live in `w`.

This is not generality for its own sake. `docs/PROCESS.md` §4 makes a flattened
realization's private state the whole logical network of the plan it came from,
so `flatten` produces a process whose `State` is strictly above the states it
was built from. With one universe that shift would drag the demand and
observation types up with it, and every demand-multiplicity and
observation-projection theorem would need transporting through a lift. With the
split, flattening moves `w` and leaves `u` alone, so those theorems transport by
identity. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.2 records the decision.

## Where the terminal-remainder law is not

An earlier version of this module gave `ProcessSpec` a `TerminalDisposition`
field, on the grounds that `docs/PROCESS.md` §2 requires a terminating run to
dispose of every outstanding demand "according to the specification's
progress/lifecycle law" and no declared field could hold that law.

That was a misreading, and it was expensive twice over. §3 already owns the
lifecycle law — `ProcessTerminationContract.disposition` and `TerminationFacet`
— and is explicit that it is a *facet* attached only when a process exports a
promise: "`ProcessCorrect` itself retains only ordinary invariant, terminal,
observation, demand, and progress facts … uncancellable leaf processes gain no
new author obligation." A mandatory field on every `ProcessSpec` is precisely
the obligation that sentence refuses. The name also collides: §3 already binds
`TerminalDisposition p state` to the per-state disposition a termination
contract produces, carrying `exactTransfer` over state, resources, loans and
obligations. That is a related concept, which is what makes reusing the name for
a second thing a `docs/README.md` one-owner violation rather than a coincidence.

The law lives in `TerminalRemainderLaw` below and is supplied through
`ProcessAcceptance`. For a *derived* acceptance — one built from a
`BehaviorContract`, or composed by a weave — that genuinely removes the
obligation from the protocol author. For a standalone protocol whose author
writes both records, it does not: it moves one field to a place where a reviewer
can see that a lifecycle claim is being made. `docs/PROCESS_IMPLEMENTATION_PLAN.md`
§10.5 records the withdrawal and this caveat.

-/

namespace Grass.Process

universe u w

/--
The optional pure projection from process state to a desired view.

`docs/PROCESS.md` §2: "An optional view facet is pure. It may be evaluated,
duplicated, coalesced, or discarded without changing platform resources or
producing an observation." That is why `render` is a function into a plain type
and not a relation into demands: a view that could emit is not a view.
-/
structure ViewFacet (State : Type w) : Type (w + 1) where
  /-- The desired-state type this process projects. -/
  View : Type w
  /-- The projection. Total and pure. -/
  render : State → View

set_option linter.checkUnivs false in
/--
One process: its interface, its state, and its relational behavior.

A vocabulary is *selected* by the `vocabulary` field rather than inherited, so
an ordinary author writes one line of interface instead of seven fields.
-/
structure ProcessSpec : Type (max (u + 1) (w + 1)) where
  /--
  The interface this process speaks, selected rather than spelled out.

  A field and not `extends`, per `agent-bus` disposition `g-design:4`: an
  ordinary author selects a reusable vocabulary in one line instead of filling
  seven interface fields inline. See the module note.
  -/
  vocabulary : ProcessVocabulary.{u}
  /-- The parameter this process is started with. -/
  Request : Type w
  /-- Private local state. Not visible to a parent; see `docs/PROCESS.md` §3. -/
  State : Type w
  /-- The typed value a terminal transition produces. -/
  TerminalResult : Type w
  /--
  The permitted initial configurations for a request: a state, the demands
  issued before any event arrives, and the observations emitted by starting.
  -/
  Initial : Request → State → Bag vocabulary.Demand →
    ObservationSegment vocabulary.Observation → Prop
  /-- The states at which this request may finish, and with what result. -/
  Terminal : Request → State → TerminalResult → Prop
  /--
  The transition relation: from a state, on an event, to a state, the demands
  this transition issues, and the observations it emits.

  The bag and the segment are the output of *this* transition only. Outstanding
  demands and the accumulated trace live in the run, not in `State`.
  -/
  Step : State → ProcessEvent vocabulary → State → Bag vocabulary.Demand →
    ObservationSegment vocabulary.Observation → Prop
  /--
  The desired-view projection, when the process has one.

  `none` is the normal choice. `docs/PROCESS.md` §2: "`view := none` is the
  normal choice for filters, servers, API calls, and other processes with no
  pure desired-state projection."
  -/
  view : Option (ViewFacet State)

namespace ProcessSpec

variable (p : ProcessSpec.{u, w})

/-! ### The interface, reached through the selected vocabulary

These are the names every consumer already used when `ProcessSpec` extended
`ProcessVocabulary`. They are abbreviations now, so moving the vocabulary behind
a field changed the author surface and not a single use site.
-/

/-- Entropy arriving from outside. -/
abbrev ExternalEvent := p.vocabulary.ExternalEvent

/-- The interactions this process asks for. -/
abbrev Demand := p.vocabulary.Demand

/-- The permitted answers to each. -/
abbrev Result := p.vocabulary.Result

/-- What the specification may observe. -/
abbrev Observation := p.vocabulary.Observation

/-- Why an outstanding demand was abandoned. -/
abbrev InterruptReason := p.vocabulary.InterruptReason

/-- How this process itself can fail. -/
abbrev LogicalFault := p.vocabulary.LogicalFault

/-- How its environment can break a contract it assumed. -/
abbrev EnvironmentViolation := p.vocabulary.EnvironmentViolation

/-- The event family of this process. -/
abbrev Event := ProcessEvent p.vocabulary

/-- The observation segment type of this process. -/
abbrev Segment := ObservationSegment p.Observation

end ProcessSpec

/--
Which partitions of a still-outstanding demand bag a terminating run may claim.

`docs/PROCESS.md` §2 requires that termination "explicitly resolves, transfers,
or permits pending for every remainder according to the specification's
progress/lifecycle law". This is that law, and the three bags are the three
outcomes the sentence names.

## Why it takes bags and not a demand

Because the obligation is a *bound*, and a bound cannot be stated against a
predicate on values. A law indexed by a single demand says which outcomes are
legitimate for a `CommitBytes`; one such permission then licenses any number of
outstanding `CommitBytes` occurrences at once, which is exactly the accounting
`docs/FOUNDATION.md` law 7 and law 20 forbid.

## What a law must constrain to bound anything

All three bags. The terminating side chooses the partition, and at this layer
`resolved`, `transferred`, and `pending` are three *labels* with no independent
content: nothing yet requires evidence that a demand placed in `resolved` was
resolved. A law reading only `pending` therefore bounds nothing — the same
occurrences can be relabelled `resolved` and the bound evaded.
`Tests/Process/M1Fixtures.lean` carries that as a negative fixture, so the trap
is written down rather than warned about.

The labels acquire content when the escrow arrives: `transferred` will name a
recipient and consume an affine resolve token, and `resolved` will carry the
completion. Until then a specification that wants a bound states it over the
whole partition.

## Why it is not a field of `ProcessSpec`

See the module note. It is supplied through `ProcessAcceptance` by whoever owns
the specification, so a leaf protocol author writes nothing.
-/
structure TerminalRemainderLaw (p : ProcessSpec.{u, w}) where
  /--
  The permitted partitions.

  `Accepts request state result resolved transferred pending` holds when a run
  of `request` finishing at `state` with `result` may claim that exactly those
  occurrences were resolved, transferred, and left pending.
  -/
  Accepts : p.Request → p.State → p.TerminalResult →
    (resolved transferred pending : Bag p.Demand) → Prop

namespace TerminalRemainderLaw

variable {p : ProcessSpec.{u, w}}

/--
The law that permits nothing: a run may only terminate holding nothing.

The strictest law, and the right default for a protocol with no lifecycle
promise. Note that it does permit termination — with all three parts empty — so
it is not vacuous in the other direction.
-/
def strict (p : ProcessSpec.{u, w}) : TerminalRemainderLaw p where
  Accepts := fun _ _ _ resolved transferred pending =>
    resolved = 0 ∧ transferred = 0 ∧ pending = 0

/--
The law that permits anything.

Present so that a specification which genuinely has no lifecycle constraint can
say so *explicitly*. A reviewer seeing this constructor knows that no terminal
custody claim is being checked; a reviewer seeing a missing field would not.
-/
def unconstrained (p : ProcessSpec.{u, w}) : TerminalRemainderLaw p where
  Accepts := fun _ _ _ _ _ _ => True

theorem strict_permits_empty (p : ProcessSpec.{u, w}) (request : p.Request)
    (state : p.State) (result : p.TerminalResult) :
    (strict p).Accepts request state result 0 0 0 := ⟨rfl, rfl, rfl⟩

theorem strict_forbids_pending (p : ProcessSpec.{u, w}) {request : p.Request}
    {state : p.State} {result : p.TerminalResult}
    {resolved transferred pending : Bag p.Demand}
    (nonempty : pending ≠ 0)
    (permitted : (strict p).Accepts request state result resolved transferred pending) :
    False := nonempty permitted.2.2

end TerminalRemainderLaw

set_option linter.checkUnivs false in
/--
The deterministic authoring convenience of `docs/PROCESS.md` §2.

`initial`, `terminal`, and `update` are functions; `toProcessSpec` derives the
relations. This is a constructor, not a second semantics: everything downstream
consumes the derived `ProcessSpec`, and `deterministic_step_functional` below is
the only extra fact it buys.
-/
structure DeterministicProcess (v : ProcessVocabulary.{u}) :
    Type (max (u + 1) (w + 1)) where
  /-- The parameter this process is started with. -/
  Request : Type w
  /-- Private local state. -/
  State : Type w
  /-- The typed value produced on termination. -/
  TerminalResult : Type w
  /-- The unique initial configuration for a request. -/
  initial : Request → State × Bag v.Demand × ObservationSegment v.Observation
  /-- Whether this state is terminal for this request, and with what result. -/
  terminal : Request → State → Option TerminalResult
  /-- The unique successor configuration for a state and event. -/
  update : State → ProcessEvent v →
    State × Bag v.Demand × ObservationSegment v.Observation
  /-- The desired-view projection, when there is one. -/
  view : Option (ViewFacet State)

namespace DeterministicProcess

variable {v : ProcessVocabulary.{u}} (d : DeterministicProcess.{u, w} v)

/-- The relational process this deterministic description denotes. -/
def toProcessSpec : ProcessSpec.{u, w} where
  vocabulary := v
  Request := d.Request
  State := d.State
  TerminalResult := d.TerminalResult
  Initial := fun request state issued emitted =>
    d.initial request = (state, issued, emitted)
  Terminal := fun request state result => d.terminal request state = some result
  Step := fun state event after issued emitted =>
    d.update state event = (after, issued, emitted)
  view := d.view

@[simp] theorem toProcessSpec_vocabulary :
    d.toProcessSpec.vocabulary = v := rfl

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
