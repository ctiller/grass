import Grass.Process.Bag
import Grass.Process.Sequential.Machine

/-!
# The sequential adapter: occurrences, pending, and child binding, generated

`docs/PROCESS.md` §4 says what an author writes — a `SequentialMachine`, which
`Grass/Process/Sequential/Machine.lean` holds — and then what happens to it:

> `SequentialAdapter.elaborateMachine` translates this syntax to the more
> general relational representation below. Because a sequential decision has at
> most one newly issued effect and its continuation is indexed by that exact
> effect's result, occurrence identity, pending multiplicity, child binding, and
> terminal disposition are generated structurally.

This module is that translation. Its target is §4's `DirectRelationalProgram`,
declared here because nothing else in the corpus declares it and the adapter is
its only producer.

## The clause that shapes the whole design

§4 ends the adapter passage with a prohibition rather than a requirement:

> Failure of those equations falls back to explicit process authoring; no
> adapter proof may weaken them to set membership or site possibility.

A prohibition on proofs is worth very little — an author can always write a
weaker theorem and give it a strong name. So it is discharged here by making the
weakened forms **unstateable** rather than merely unproved, in two moves.

**`Pending` is derived, not supplied.** §4 lists `Pending : State ->
AbstractDemandBag (EffectDemand boundary)` as a field alongside a
`transitionEquation` connecting it to the step outputs. Here `held : State → Bag
Occurrence` is the field and `Pending` is `held` mapped through the occurrence's
demand. A program therefore cannot present a demand bag that disagrees with its
occurrences, because it never presents one; and equal-valued demands keep their
multiplicity because they arrive from distinct occurrences through `Bag.map`,
which preserves cardinality (`Bag.card_map`).

**A delivered result names an occurrence, not a demand.** `DirectEvent.result`
carries the exact `Occurrence` being answered and an answer typed by *that
occurrence's* demand. Consumption is then `ConsumeExactlyOneMatching` on the
occurrence bag, which `Grass/Process/Bag.lean` already argues is the form that
forbids fabrication, duplication, joint consumption and loss. "Set membership"
is not a weaker proof of the same statement here — it is not a statement about
the same objects.

## What a sequential machine's occurrences are

The identity has to distinguish two issues of the same demand from the same
state, because a retry loop — `decide s = .effect d (fun _ => s)` — is an
ordinary machine and issues `d` at `s` unboundedly often. Identifying an
occurrence by its state would collapse those, and identifying it by its demand
would collapse more.

So the elaborated state is a `SequentialPoint`: the machine's state and how many
steps the execution has taken. An occurrence is a point together with the demand
and continuation the machine decides there, and `occurrence_determined_by_point`
proves the last two are redundant — the point alone fixes them. That is §4's
"generated structurally": the author supplied no identity and the adapter
invented no choice.

## What this elaboration cannot express, stated rather than hidden

A sequential machine holds **at most one** outstanding occurrence, because the
only way to hold one is to be blocked on it (`held_card_le_one`). Two
consequences follow and both are real limits rather than conveniences:

* it cannot reach a terminal state with anything outstanding
  (`terminal_holds_nothing`), so its terminal disposition is the empty partition
  and §3's "resolve, transfer, or permit" has no work to do here;
* every step empties the pending bag before refilling it
  (`remainder_is_empty`), which is why the pending equation below has
  `remainder = 0` in both cases.

`docs/FOUNDATION.md` law 17 permits exactly this: "serial authoring may
synthesize a degenerate process realization, but it may not introduce an
alternate semantics or theorem route." The degeneracy is the one-outstanding
bound. What is *not* degenerate is the equation it satisfies, which is the
general one.
-/

namespace Grass.Process

open Grass.Specification

universe u

/-! ## The events a direct relational program consumes -/

/--
What drives one step: an internal decision, or a result delivered to one exact
outstanding occurrence.

Parameterised by the occurrence type and its demand assignment so that
`answer`'s type is the result type of *that occurrence's* demand. An event
carrying a demand rather than an occurrence would be the "set membership"
weakening §4 forbids: with two outstanding occurrences of equal demand there
would be no fact of the matter about which one was answered.
-/
inductive DirectEvent (boundary : DriverBoundary.{u}) (Occurrence : Type u)
    (demandOf : Occurrence → EffectDemand boundary) : Type u
  /-- The program moved on its own. -/
  | internal
  /-- The environment answered one outstanding occurrence. -/
  | result (occurrence : Occurrence) (answer : EffectResult (demandOf occurrence))

namespace DirectEvent

variable {boundary : DriverBoundary.{u}} {Occurrence : Type u}
  {demandOf : Occurrence → EffectDemand boundary}

/--
What a step consumes, as an equation on the outstanding bag.

Not a membership side condition: for a delivered result this is
`Bag.ConsumeExactlyOneMatching`, which removes exactly one `cons` and keeps the
whole rest as `remainder`.
-/
def Consumes (event : DirectEvent boundary Occurrence demandOf)
    (outstanding remainder : Bag Occurrence) : Prop :=
  match event with
  | .internal => remainder = outstanding
  | .result occurrence _ => Bag.ConsumeExactlyOneMatching outstanding occurrence remainder

/-- An internal step consumes nothing. -/
@[simp] theorem consumes_internal {outstanding remainder : Bag Occurrence} :
    (DirectEvent.internal (boundary := boundary) (demandOf := demandOf)).Consumes
      outstanding remainder ↔ remainder = outstanding := Iff.rfl

/-- A result step consumes exactly the occurrence it answers. -/
@[simp] theorem consumes_result {occurrence : Occurrence}
    {answer : EffectResult (demandOf occurrence)} {outstanding remainder : Bag Occurrence} :
    (DirectEvent.result (boundary := boundary) occurrence answer).Consumes
      outstanding remainder ↔
      Bag.ConsumeExactlyOneMatching outstanding occurrence remainder := Iff.rfl

/--
Consumption determines the remainder.

The property that makes the pending equation an equation rather than a
constraint: given the step and the bag before it, there is at most one bag
after, so a proof cannot pick a convenient remainder.
-/
theorem Consumes.remainder_unique {event : DirectEvent boundary Occurrence demandOf}
    {outstanding left right : Bag Occurrence}
    (first : event.Consumes outstanding left) (second : event.Consumes outstanding right) :
    left = right := by
  cases event with
  | internal => exact first.trans second.symm
  | result occurrence _ => exact Bag.ConsumeExactlyOneMatching.remainder_unique first second

/-- Consumption never grows the bag. -/
theorem Consumes.card_le {event : DirectEvent boundary Occurrence demandOf}
    {outstanding remainder : Bag Occurrence}
    (consumes : event.Consumes outstanding remainder) :
    remainder.card ≤ outstanding.card := by
  cases event with
  | internal => exact Nat.le_of_eq (congrArg Bag.card consumes)
  | result occurrence _ =>
    have counted := Bag.ConsumeExactlyOneMatching.card consumes
    omega

end DirectEvent

/-! ## The relational program the adapter produces -/

/--
A terminal state's account of every occurrence it still holds.

`docs/PROCESS.md` §3: "termination explicitly resolves, transfers, or permits
pending". The same three-way partition `Grass/Process/Run.lean`'s
`TerminalDemandClassification` uses, over occurrences rather than demand values
and without the specification's acceptance law — a program is not a
specification, so it can account for what it holds but cannot say whether that
account is permitted.
-/
structure DemandDisposition {Occurrence : Type u} (outstanding : Bag Occurrence) : Type u where
  /-- The occurrences claimed answered. -/
  resolved : Bag Occurrence
  /-- The occurrences whose custody passes elsewhere. -/
  transferred : Bag Occurrence
  /-- The occurrences left unanswered. -/
  pending : Bag Occurrence
  /-- Every held occurrence is in exactly one part, and none is invented. -/
  partition : outstanding = resolved + transferred + pending

/--
`docs/PROCESS.md` §4's `DirectRelationalProgram`: the relational representation
the adapter elaborates a sequential machine into.

Two departures from the declaration, both narrowing rather than widening:

* §4's `Pending` field is `held` here, a bag of *occurrences*, and `Pending` is
  derived from it. See the module note — this is what makes the "no weakening to
  set membership" clause structural.
* §4's `sites : FiniteDependentEffectSiteInventory Initial Step` is absent. A
  finite syntactic inventory of possible effect sites is exactly what §4 says
  must not be confused with the effects a particular execution issues, and this
  layer has no use for one: `held` reports the occurrences an execution actually
  holds. A later module that needs an inventory — for code generation, say —
  should add it as an independent claim, not as a field this structure would let
  a producer assert unchecked.
-/
structure DirectRelationalProgram (boundary : DriverBoundary.{u}) : Type (u + 1) where
  /-- The program's state. -/
  State : Type u
  /-- What it is started with. -/
  Request : Type u
  /-- What it finishes with. -/
  TerminalResult : Type u
  /-- The identities of the effects its executions issue. -/
  Occurrence : Type u
  /-- Each occurrence's exact demand: §4's site and protocol half of the binding. -/
  demandOf : Occurrence → EffectDemand boundary
  /--
  And the continuation it is bound to: §4's child half.

  Total on that exact occurrence's result type, which is `docs/FOUNDATION.md`
  law 5 — a binding that handled some results and left others to a later proof
  would not typecheck.
  -/
  resumeOf : (occurrence : Occurrence) → EffectResult (demandOf occurrence) → State
  /-- The occurrences a state is holding, with multiplicity. -/
  held : State → Bag Occurrence
  /-- Starting: the exact occurrences issued and observations emitted. -/
  Initial : Request → State → Bag Occurrence → ObservationSegment boundary.Observation → Prop
  /-- Stepping: likewise, for the execution this event drove. -/
  Step : State → DirectEvent boundary Occurrence demandOf → State → Bag Occurrence ->
    ObservationSegment boundary.Observation → Prop
  /-- §4's `initialEquation`: a start's issued bag is what the start holds. -/
  initialEquation : ∀ request state issued observations,
    Initial request state issued observations → held state = issued
  /--
  §4's `transitionEquation`, exact in both directions of the bag.

  `remainder` is the whole rest of the bag rather than an arbitrary sub-bag, and
  `held after` is an equation rather than a containment, so nothing is lost,
  duplicated or invented across a step.
  -/
  transitionEquation : ∀ before event after issued observations,
    Step before event after issued observations ->
    ∃ remainder, event.Consumes (held before) remainder ∧ held after = remainder + issued
  /--
  §4's `ExactSiteProtocolAndChildBinding`, as a law on steps rather than a
  lookup: the state a delivered result lands in is exactly the one the answered
  occurrence's own continuation gives.

  Stated over the step rather than over the occurrence because that is where it
  can be violated — a program could carry a perfectly good `resumeOf` and then
  step somewhere else.
  -/
  stepBinding : ∀ before occurrence answer after issued observations,
    Step before (.result occurrence answer) after issued observations ->
    after = resumeOf occurrence answer
  /-- Finishing. -/
  terminal : Request → State → TerminalResult → Prop
  /-- §4's `EveryTerminalStateClassifiesEveryPendingOccurrence`. -/
  terminalDisposition : ∀ request state result, terminal request state result ->
    DemandDisposition (held state)

namespace DirectRelationalProgram

variable {boundary : DriverBoundary.{u}} (program : DirectRelationalProgram boundary)

/--
§4's `Pending`, derived rather than supplied.

A program cannot present a demand bag that disagrees with its occurrences,
because it never presents one.
-/
def Pending (state : program.State) : Bag (EffectDemand boundary) :=
  (program.held state).map program.demandOf

/--
**Multiplicity survives the projection to demands.**

The concrete content of "equal-valued demands retain multiplicity through
distinct occurrences": two held occurrences of the same demand give a pending
bag of cardinality two, not one. `Bag.card_map` is what makes this immediate,
and a set-valued `Pending` is what would make it false.
-/
@[simp] theorem card_pending (state : program.State) :
    (program.Pending state).card = (program.held state).card :=
  Bag.card_map ..

variable {program}

/--
The demand-level pending equation for a delivered result.

A corollary of the occurrence-level one, and deliberately *derived* rather than
stated as the primitive: `Bag.map_consume` transports the exact consumption, so
the demand-level statement inherits its exactness instead of asserting a weaker
one alongside it.
-/
theorem pending_equation_of_result {before after : program.State}
    {occurrence : program.Occurrence}
    {answer : EffectResult (program.demandOf occurrence)}
    {issued : Bag program.Occurrence} {observations : ObservationSegment boundary.Observation}
    (step : program.Step before (.result occurrence answer) after issued observations) :
    ∃ remainder, Bag.ConsumeExactlyOneMatching (program.Pending before)
        (program.demandOf occurrence) remainder /\
      program.Pending after = remainder + issued.map program.demandOf := by
  obtain ⟨remainder, consumes, equation⟩ :=
    program.transitionEquation before _ after issued observations step
  refine ⟨remainder.map program.demandOf, Bag.map_consume _ consumes, ?_⟩
  simp only [Pending, equation, Bag.map_add]

/-- And for an internal step, which consumes nothing. -/
theorem pending_equation_of_internal {before after : program.State}
    {issued : Bag program.Occurrence} {observations : ObservationSegment boundary.Observation}
    (step : program.Step before .internal after issued observations) :
    program.Pending after = program.Pending before + issued.map program.demandOf := by
  obtain ⟨remainder, consumes, equation⟩ :=
    program.transitionEquation before _ after issued observations step
  simp only [DirectEvent.consumes_internal] at consumes
  simp only [Pending, equation, consumes, Bag.map_add]

end DirectRelationalProgram

/-! ## Elaborating a sequential machine -/

namespace SequentialMachine

variable {boundary : DriverBoundary.{u}} (machine : SequentialMachine boundary)

/--
Where an execution is: the machine's state, and how many steps it took to get
there.

The `age` is the whole of the occurrence-identity design, so it is worth saying
what it buys. A retry loop — `decide s = .effect d (fun _ => s)` — issues `d`
from `s` unboundedly often. Identifying an occurrence by its state would make
every one of those issues the same occurrence, and the pending bag would then be
blind to exactly the multiplicity `docs/PROCESS.md` §4 requires it to keep.
-/
structure Point : Type u where
  /-- How many steps the execution has taken. -/
  age : Nat
  /-- Where it is. -/
  state : machine.State

/--
An effect occurrence: an execution point, with the demand issued there and the
continuation bound to it.

The demand and continuation are fields rather than derived, so the type carries
no proof and `held` below needs no dependent match. Nothing is lost by that:
`held_issues` proves every occurrence the adapter produces really is decided by
the machine, and `issuing_occurrence_determined_by_point` proves the fields are
redundant for those — the point alone fixes them. An `Occurrence` that satisfies
neither is a value nothing constructs, and the fixtures use exactly that to show
the adapter does not invent occurrences.
-/
structure Occurrence : Type u where
  /-- Where it was issued. -/
  point : machine.Point
  /-- What was issued. -/
  demand : EffectDemand boundary
  /-- What the answer resumes into. -/
  resume : EffectResult demand → machine.State

/-- The demand assignment, as a function, for indexing events. -/
abbrev occurrenceDemand : machine.Occurrence → EffectDemand boundary := Occurrence.demand

/-- The events that drive an elaborated sequential machine. -/
abbrev Event : Type u := DirectEvent boundary machine.Occurrence machine.occurrenceDemand

variable {machine}

/-- An occurrence the machine really decides at its own point. -/
def Occurrence.Issues (occurrence : machine.Occurrence) : Prop :=
  machine.decide occurrence.point.state = .effect occurrence.demand occurrence.resume

variable (machine)

/--
The occurrences a point holds: the one it is blocked on, or none.

A plain match on the decision, which is what makes it a total function needing
no choice and no proof argument.
-/
def held (point : machine.Point) : Bag machine.Occurrence :=
  match machine.decide point.state with
  | .effect demand resume => {⟨point, demand, resume⟩}
  | .internal _ _ => 0
  | .terminal _ => 0

variable {machine}

theorem held_of_effect {point : machine.Point} {demand : EffectDemand boundary}
    {resume : EffectResult demand → machine.State}
    (decision : machine.decide point.state = .effect demand resume) :
    machine.held point = {⟨point, demand, resume⟩} := by
  unfold held; rw [decision]

theorem held_of_internal {point : machine.Point} {next : machine.State}
    {observations : ObservationSegment boundary.Observation}
    (decision : machine.decide point.state = .internal next observations) :
    machine.held point = 0 := by
  unfold held; rw [decision]

theorem held_of_terminal {point : machine.Point} {result : machine.Terminal}
    (decision : machine.decide point.state = .terminal result) :
    machine.held point = 0 := by
  unfold held; rw [decision]

/--
**A point holds at most one occurrence.**

The degeneracy law 17 permits, stated rather than left implicit: a sequential
machine is blocked on one effect or on none, so it can never exhibit the
multiplicity a general network can. Everything below is exact anyway, which is
the point — the equations do not become easier, only the bags become smaller.
-/
theorem held_card_le_one (point : machine.Point) : (machine.held point).card ≤ 1 := by
  unfold held
  split <;> simp [Bag.singleton_eq]

/-- **And every occurrence it holds is one the machine really issues.** -/
theorem held_issues {point : machine.Point} {occurrence : machine.Occurrence}
    (present : occurrence ∈ machine.held point) : occurrence.Issues := by
  unfold held at present
  split at present
  · rename_i demand resume decision
    rw [Bag.mem_singleton] at present
    subst present
    exact decision
  · exact absurd present (by simp)
  · exact absurd present (by simp)

/-- A held occurrence's point is the point holding it. -/
theorem held_point {point : machine.Point} {occurrence : machine.Occurrence}
    (present : occurrence ∈ machine.held point) : occurrence.point = point := by
  unfold held at present
  split at present
  · rw [Bag.mem_singleton] at present
    subst present
    rfl
  · exact absurd present (by simp)
  · exact absurd present (by simp)

/--
**An issuing occurrence is determined by its point.**

`docs/PROCESS.md` §4's "occurrence identity ... generated structurally", as a
theorem: an author supplied no identity, and the adapter had no choice to make,
because the demand and the continuation are functions of where the execution is.

This is also the child-binding uniqueness a fixture checks — two bindings for
one occurrence are the same binding.
-/
theorem issuing_occurrence_determined_by_point {left right : machine.Occurrence}
    (leftIssues : left.Issues) (rightIssues : right.Issues)
    (samePoint : left.point = right.point) : left = right := by
  obtain ⟨leftPoint, leftDemand, leftResume⟩ := left
  obtain ⟨rightPoint, rightDemand, rightResume⟩ := right
  simp only at samePoint
  subst samePoint
  simp only [Occurrence.Issues] at leftIssues rightIssues
  rw [leftIssues] at rightIssues
  injection rightIssues with demandEq resumeEq
  subst demandEq
  simp only [Occurrence.mk.injEq, heq_eq_eq, true_and]
  exact eq_of_heq resumeEq

/-! ### The step relation -/

variable (machine)

/--
One step of the elaborated machine.

`held before = {occurrence}` rather than `occurrence ∈ machine.held before` is
deliberate and is the same choice as everywhere else here: membership would
admit answering an occurrence while others stayed outstanding without saying
what happened to them, and the equation does not.
-/
def Drives (before : machine.Point) (event : machine.Event) (after : machine.Point)
    (issued : Bag machine.Occurrence)
    (observations : ObservationSegment boundary.Observation) : Prop :=
  after.age = before.age + 1 ∧ issued = machine.held after /\
    match event with
    | .internal => machine.decide before.state = .internal after.state observations
    | .result occurrence answer =>
        machine.held before = {occurrence} ∧ after.state = occurrence.resume answer /\
          observations = []

/--
The elaboration.

Every field is generated from `decide`. Nothing here consults the author for an
occurrence identity, a child binding, a pending bag, or a disposition.
-/
def elaborate : DirectRelationalProgram boundary where
  State := machine.Point
  Request := machine.Request
  TerminalResult := machine.Terminal
  Occurrence := machine.Occurrence
  demandOf := machine.occurrenceDemand
  resumeOf := fun occurrence answer => ⟨occurrence.point.age + 1, occurrence.resume answer⟩
  held := machine.held
  Initial := fun request point issued observations =>
    point = ⟨0, machine.initial request⟩ ∧ issued = machine.held point ∧ observations = []
  Step := machine.Drives
  initialEquation := by
    rintro request point issued observations ⟨_, issuedEq, _⟩
    exact issuedEq.symm
  transitionEquation := by
    rintro before event after issued observations ⟨_, issuedEq, drives⟩
    cases event with
    | internal =>
      refine ⟨machine.held before, rfl, ?_⟩
      rw [held_of_internal drives, issuedEq, Bag.zero_add]
    | result occurrence answer =>
      obtain ⟨heldBefore, _, _⟩ := drives
      refine ⟨0, ?_, ?_⟩
      · show machine.held before = Bag.cons occurrence 0
        rw [heldBefore, Bag.singleton_eq]
        rfl
      · rw [issuedEq, Bag.zero_add]
  stepBinding := by
    rintro before occurrence answer after issued observations ⟨age, _, heldBefore, resumed, _⟩
    have atBefore : occurrence.point = before :=
      held_point (by rw [heldBefore]; simp)
    obtain ⟨afterAge, afterState⟩ := after
    simp only at age resumed
    subst age
    subst resumed
    rw [atBefore]
  terminal := fun _ point result => machine.decide point.state = .terminal result
  terminalDisposition := by
    intro _ point result decision
    exact ⟨0, 0, 0, by rw [held_of_terminal decision]; simp⟩

variable {machine}

/-! ### What the elaboration is worth -/

/-- The elaborated `Pending` is the demand the machine is blocked on, or none. -/
theorem pending_of_effect {point : machine.Point} {demand : EffectDemand boundary}
    {resume : EffectResult demand → machine.State}
    (decision : machine.decide point.state = .effect demand resume) :
    (machine.elaborate).Pending point = {demand} := by
  show ((machine.held point).map machine.occurrenceDemand) = {demand}
  rw [held_of_effect decision]
  rfl

/--
**A sequential machine cannot finish holding anything.**

Stated as a limit rather than presented as a convenience. `docs/PROCESS.md` §3
requires termination to "explicitly resolve, transfer, or permit pending", and
here the requirement is discharged by there being nothing to dispose of — which
is true of this authoring surface and false of the general network, so a reader
must not carry it across.
-/
theorem terminal_holds_nothing {point : machine.Point} {result : machine.Terminal}
    (decision : machine.decide point.state = .terminal result) :
    (machine.elaborate).Pending point = 0 := by
  show ((machine.held point).map machine.occurrenceDemand) = 0
  rw [held_of_terminal decision]
  rfl

/--
**The step relation is exactly `Drives`, in both directions.**

The direction a fixture usually checks is that the machine's decision produces
an elaborated step. The direction that has teeth is the other one: the
elaboration admits *no other* steps, so a fixture that pins the after-state and
the issued bag has pinned the whole relation rather than one witness of it.
-/
theorem elaborate_step_iff {before after : machine.Point} {event : machine.Event}
    {issued : Bag machine.Occurrence}
    {observations : ObservationSegment boundary.Observation} :
    (machine.elaborate).Step before event after issued observations <->
      machine.Drives before event after issued observations := Iff.rfl

/-- The elaborated program's child binding is the occurrence's own continuation. -/
theorem elaborate_resumeOf (occurrence : machine.Occurrence)
    (answer : EffectResult occurrence.demand) :
    (machine.elaborate).resumeOf occurrence answer =
      ⟨occurrence.point.age + 1, occurrence.resume answer⟩ := rfl

end SequentialMachine

end Grass.Process
