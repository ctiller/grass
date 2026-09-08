import Grass.Process.Spec

/-!
# Serial calls: what may collapse into one process transition

`docs/PROCESS.md` §3 draws the line this module is about:

> A process step may call a proved serial function directly. It does not create
> a child instance, channel, demand occurrence, or scheduling point merely
> because the machine realization uses an ABI `call`.

and then says where the line is:

> The boundary is semantic. A computation which can wait for external entropy,
> remain pending, be independently cancelled, transfer resources or obligations
> to another custodian, or interleave observably must expose the corresponding
> demand/child/frontier.

## Where `noFrontier` went

§3's `SerialFunctionContract` ends with `noFrontier :
NoExternalPendingCancellationOrInterleavingFrontier`, and there is no such
field here. It would be an opaque promise: an author writes `noFrontier := ⟨⟩`
and nothing checks it, which is the shape `docs/DECISIONS.md` decision 131
rejected for `ChannelContract`.

What replaces it is **not** the shape of `SerialDecision` on its own. A first
draft claimed exactly that — two constructors where `SequentialDecision` has
three, so a serial function "cannot decide to wait" — and local adversarial
review took it apart in two moves. The claim was true about
`SerialFunctionSource` and irrelevant, because `CollapsesToOneTransition` was
indexed by a *contract* and never mentioned a source; and a contract's `Post`
admits external entropy directly, by relating a before-state to more than one
after-state and letting the environment pick.

So the frontier-freedom argument now runs through the collapse itself:

* `CollapsesToOneTransition` requires a `SerialFunctionSource` **and** a
  `SerialFunctionRealizes` relating it to the contract. There is no collapse
  without a machine.
* `SerialFunctionRealizes.converse` requires every state the contract's `Post`
  permits to be one the machine actually reaches — §3's `converse` field, and
  the load-bearing one.
* `decide` is a function of the machine state, so from one entry the machine
  reaches at most one exit (`exit_is_unique`). With `converse`, `Post` is
  therefore **single-valued**: `post_is_determined`.

`a_call_that_can_answer_two_ways_is_not_serial` is that as a refusal. A
`blockingRead` whose post-state depends on how many bytes arrived has no
realizing source, so it has no collapse, so it stays a frontier — which is §3's
"a synchronous platform API is still modeled by a child protocol because its
return is external entropy".

## What is still a field, and why

`Post`, `obligations`, `resources`, and `faultCustody` are the content of the
contract and nothing structural can supply them. What review showed is that
being a field is not enough on its own:

* `footprintAgrees` is a relation the same author supplies as `Post`, so
  `fun _ _ => True` discharged `postWithinFootprint` by `trivial`.
  `footprintSeparates` forbids exactly that. It does not make the footprint
  *right*, and see §10.31 for what would.
* `workBound` was `present` without §3's `and proved`, so any contract could
  claim a zero-work latency bound by writing one field.
  `SerialFunctionRealizes.bounded` is the missing proof, and `Responsive` now
  has `responsive_is_realized` behind it.
* `faultCustody` quoted §3's "resource custody, obligation custody, and any
  partial mutation" while its arity mentioned neither ledger. It now takes all
  three.

## What this module still does not do

It does not prove §3's `FiniteStutteringCallSimulation` against a *machine* ABI
— `bounded`'s step count is the source's, not an instruction count, and there is
no ghost erasure or encoding here. Of that structure's nine fields, `entry`,
`exit`, `converse`, `custody`, `rank` and `visibility` are stated here against
`SerialFunctionSource`; `internal` and `bounded` are stated in the weaker
source-relative form; `partialMutation` is `faultCustody`. The ABI half is
`docs/MACHINE.md`'s.

`SerialCallVisibility`'s `Exclusive`, `LinearizesAt` and `Noninterference` are
parameters supplied by the surrounding plan, and nothing here ties `Exclusive`
to `footprintAgrees`. §3 writes `CallerExclusivelyOwns contract.footprint`, so
that tie is real and missing; it needs the surrounding network's ownership
discipline, which is the memory layer's. Recorded as §10.32 rather than
approximated.
-/

namespace Grass.Process

universe u w

/-! ## How a serial call ends -/

/--
How a serial call finished.

`docs/PROCESS.md` §3's `SerialCallDisposition`. Two constructors and no third:
§3 says "there is no generic exceptional edge whose state is left implicit", and
an edge that is neither a return nor a raise would be exactly that.
-/
inductive SerialCallDisposition (Output Fault : Type w) : Type w
  /-- It returned a value. -/
  | returned (value : Output)
  /-- It raised a fault. -/
  | raised (value : Fault)

/-! ## What a serial function decides -/

/--
What a serial function does at a state.

**Two constructors, where `SequentialDecision` has three.** The missing one is
`.effect demand resume`. That is a real difference and it is what makes
`exit_is_unique` provable; it is not, on its own, the frontier-freedom argument
— see the module note.
-/
inductive SerialDecision (State ExitState : Type w) : Type w
  /-- Keep going. -/
  | internal (next : State)
  /-- Stop, at a declared exit. -/
  | exit (state : ExitState)

namespace SerialDecision

variable {State ExitState : Type w}

/-- A decision is an exit, or it is internal. There is no third case. -/
def IsExit : SerialDecision State ExitState → Prop
  | .internal _ => False
  | .exit _ => True

/--
No decision waits.

True of the type, and worth exactly what the module note says it is worth: it
gives `exit_is_unique`, and the frontier argument needs `converse` as well.
-/
theorem no_waiting_decision (decision : SerialDecision State ExitState) :
    (∃ next, decision = .internal next) ∨ ∃ state, decision = .exit state := by
  cases decision with
  | internal next => exact Or.inl ⟨next, rfl⟩
  | exit state => exact Or.inr ⟨state, rfl⟩

end SerialDecision

/-! ## The contract -/

/--
`docs/PROCESS.md` §3's `SerialFunctionContract`, over a process's logical state.
-/
structure SerialFunctionContract (State : Type w) : Type (w + 1) where
  /-- What the call is given. -/
  Input : Type w
  /-- What it returns. -/
  Output : Type w
  /-- What it may raise. -/
  Fault : Type w
  /-- The states it may stop at. -/
  ExitState : Type w
  /-- The local obligation state it transforms. -/
  Obligations : Type w
  /-- The local resource state it transforms. -/
  Resources : Type w
  /-- When it may be called. -/
  Pre : Input → State → Prop
  /-- What each exit means. -/
  disposition : ExitState → SerialCallDisposition Output Fault
  /-- The state transformation each exit performs. -/
  Post : Input → ExitState → State → State → Prop
  /-- Its obligation transformation. -/
  obligations : Input → ExitState → Obligations → Obligations → Prop
  /-- Its resource transformation. -/
  resources : Input → ExitState → Resources → Resources → Prop
  /--
  Two states agree outside what this call may touch.

  §3's `footprint : LogicalFootprint`, carried as the relation a footprint
  *induces* rather than as an opaque handle.
  -/
  footprintAgrees : State → State → Prop
  /-- **And the call really stays inside it.** -/
  postWithinFootprint : ∀ input exit before after,
    Post input exit before after → footprintAgrees before after
  /--
  **And the footprint separates something.**

  Without this, `footprintAgrees := fun _ _ => True` discharges
  `postWithinFootprint` by `trivial` and the footprint bounds nothing —
  `Grass/Process/Network/Assertion.lean` records the same failure for
  `NetworkAssertion.framed`, where the fix was `agreesGlue`.

  This is weaker than `agreesGlue`: it forbids the degenerate footprint without
  forcing the declared one to be the real one. Doing better needs the footprint
  to range over *fragments* of the state rather than over the state as a whole,
  which this layer cannot express — see
  `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.31.
  -/
  footprintSeparates : ∃ left right, ¬ footprintAgrees left right
  /--
  The mutation and custody a raised fault leaves behind.

  All three ledgers, because §3 asks for all three: "Each exit fixes the logical
  post-state, resource custody, obligation custody, and any partial mutation;
  there is no generic exceptional edge whose state is left implicit." An earlier
  version took only the state and quoted that sentence anyway.
  -/
  faultCustody : Fault → State → Obligations → Resources →
    State → Obligations → Resources → Prop
  /-- **And a raised fault declares its exact partial mutation and custody.** -/
  faultsDeclared : ∀ input exit fault
      before beforeObligations beforeResources
      after afterObligations afterResources,
    disposition exit = .raised fault →
    Post input exit before after →
    obligations input exit beforeObligations afterObligations →
    resources input exit beforeResources afterResources →
    faultCustody fault before beforeObligations beforeResources
      after afterObligations afterResources
  /-- The carrier of the internal measure. -/
  Rank : Type w
  /-- Its strict order. -/
  rankLt : Rank → Rank → Prop
  /-- No infinite internal descent. -/
  rankWellFounded : WellFounded rankLt
  /--
  A numeric work bound, when a product responsiveness theorem needs one.

  §3: "bare termination is not silently promoted to a latency bound." `none` is
  the ordinary case, and a `some` is not self-certifying —
  `SerialFunctionRealizes.bounded` is what makes it a claim about a machine
  rather than a number an author wrote.
  -/
  workBound : Option (Input → State → Nat)

namespace SerialFunctionContract

variable {State : Type w} (contract : SerialFunctionContract State)

/-- The contract claims a numeric work bound. -/
def Responsive : Prop := ∃ bound, contract.workBound = some bound

/--
Termination does not give a work bound.

The `Option` is doing real work, and this is the trivial half of why: `none` is
not `some`. The half with content is `responsive_is_realized`, which says a
`some` has been proved against a machine.
-/
theorem terminating_is_not_bounded (noBound : contract.workBound = none) :
    ¬ contract.Responsive := by
  rintro ⟨bound, isSome⟩
  rw [noBound] at isSome
  exact absurd isSome (by simp)

variable {contract}

/-- A returning exit. -/
def Returns (exit : contract.ExitState) : Prop :=
  ∃ value, contract.disposition exit = .returned value

/-- A raising exit. -/
def Raises (exit : contract.ExitState) : Prop :=
  ∃ value, contract.disposition exit = .raised value

/--
**Every exit is one or the other.**

`docs/PROCESS.md` §3's "there is no generic exceptional edge whose state is left
implicit", at the disposition: a third kind of exit is not expressible, so there
is no edge for which `faultsDeclared` neither applies nor needs to.
-/
theorem exit_returns_or_raises (exit : contract.ExitState) :
    Returns exit ∨ Raises exit := by
  match decision : contract.disposition exit with
  | .returned value => exact Or.inl ⟨value, decision⟩
  | .raised value => exact Or.inr ⟨value, decision⟩

/-- **And a raising exit's mutation and custody are declared.** -/
theorem raising_exit_declares_its_custody {exit : contract.ExitState}
    (raises : Raises exit) {input : contract.Input}
    {before after : State}
    {beforeObligations afterObligations : contract.Obligations}
    {beforeResources afterResources : contract.Resources}
    (post : contract.Post input exit before after)
    (movedObligations : contract.obligations input exit beforeObligations afterObligations)
    (movedResources : contract.resources input exit beforeResources afterResources) :
    ∃ fault, contract.faultCustody fault before beforeObligations beforeResources
      after afterObligations afterResources := by
  obtain ⟨fault, isRaised⟩ := raises
  exact ⟨fault, contract.faultsDeclared input exit fault before beforeObligations
    beforeResources after afterObligations afterResources isRaised post
    movedObligations movedResources⟩

end SerialFunctionContract

/-! ## A function as a machine -/

/--
A serial function's internal structure.

`read` is what makes this relatable to the contract at all: a machine state
represents a logical state, and `enterReads` says entering represents the state
the call was made at. Without it `enter` was a field nothing consumed, and
`reaches_an_exit` reached an exit with no connection to the caller's `Post`.
-/
structure SerialFunctionSource {State : Type w}
    (contract : SerialFunctionContract State) : Type (w + 1) where
  /-- The function's own working state. -/
  Machine : Type w
  /-- Where it starts. -/
  enter : contract.Input → State → Machine
  /-- The logical state a machine state represents. -/
  read : Machine → State
  /-- Entering represents the state the call was made at. -/
  enterReads : ∀ input before, read (enter input before) = before
  /-- What it does at a state. -/
  decide : Machine → SerialDecision Machine contract.ExitState
  /-- Its internal measure. -/
  rank : Machine → contract.Rank
  /-- **Internal decisions strictly decrease it.** -/
  internalDecreases : ∀ state next,
    decide state = .internal next → contract.rankLt (rank next) (rank state)

namespace SerialFunctionSource

variable {State : Type w} {contract : SerialFunctionContract State}
  (source : SerialFunctionSource contract)

/-- One internal step. -/
def InternalStep (before after : source.Machine) : Prop :=
  source.decide before = .internal after

/-- Zero or more. -/
inductive InternalSteps (source : SerialFunctionSource contract) :
    source.Machine → source.Machine → Prop
  /-- None. -/
  | refl (state : source.Machine) : InternalSteps source state state
  /-- One more. -/
  | step {start middle finish : source.Machine}
      (first : source.InternalStep start middle)
      (rest : InternalSteps source middle finish) : InternalSteps source start finish

/-- Zero or more, within a step budget. -/
inductive InternalStepsWithin (source : SerialFunctionSource contract) :
    Nat → source.Machine → source.Machine → Prop
  /-- None, with any budget left. -/
  | refl (fuel : Nat) (state : source.Machine) : InternalStepsWithin source fuel state state
  /-- One more, spending one unit. -/
  | step {fuel : Nat} {start middle finish : source.Machine}
      (first : source.InternalStep start middle)
      (rest : InternalStepsWithin source fuel middle finish) :
      InternalStepsWithin source (fuel + 1) start finish

/-- A budgeted execution is an execution. -/
theorem InternalStepsWithin.toSteps {fuel : Nat} {start finish : source.Machine}
    (bounded : source.InternalStepsWithin fuel start finish) :
    source.InternalSteps start finish := by
  induction bounded with
  | refl _ state => exact .refl state
  | step first _ ih => exact .step first ih

/--
**Every maximal internal execution reaches an exit.**

`docs/PROCESS.md` §3's `EveryMaximalInternalExecutionHasExactlyOneDeclaredExit`,
at the "reaches" half. `exit_is_unique` is the "exactly one" half, which an
earlier version of this module claimed in prose and did not state.
-/
theorem reaches_an_exit (state : source.Machine) :
    ∃ finish, source.InternalSteps state finish ∧ (source.decide finish).IsExit := by
  induction hypothesis : source.rank state using
      contract.rankWellFounded.induction generalizing state with
  | _ current ih =>
    match decision : source.decide state with
    | .internal next =>
      obtain ⟨finish, steps, isExit⟩ :=
        ih (source.rank next) (hypothesis ▸ source.internalDecreases state next decision)
          next rfl
      exact ⟨finish, .step decision steps, isExit⟩
    | .exit exitState => exact ⟨state, .refl state, by rw [decision]; exact trivial⟩

variable {source}

/--
**And it reaches exactly one.**

`decide` is a function of the machine state and an exit has no successor, so the
execution from a given entry is a chain with one endpoint. This is what makes
`post_is_determined` work, and through it the whole frontier-freedom argument.
-/
theorem exit_is_unique {start finishLeft finishRight : source.Machine}
    (left : source.InternalSteps start finishLeft)
    (leftExit : (source.decide finishLeft).IsExit)
    (right : source.InternalSteps start finishRight)
    (rightExit : (source.decide finishRight).IsExit) : finishLeft = finishRight := by
  induction left generalizing finishRight with
  | refl state =>
    cases right with
    | refl _ => rfl
    | step first _ =>
      rw [show source.decide state = _ from first] at leftExit
      exact absurd leftExit id
  | step first _ ih =>
    cases right with
    | refl _ =>
      rw [show source.decide _ = _ from first] at rightExit
      exact absurd rightExit id
    | step firstRight restRight =>
      have same : SerialDecision.internal _ = SerialDecision.internal _ :=
        Eq.trans (Eq.symm first) firstRight
      injection same with sameMiddle
      subst sameMiddle
      exact ih leftExit restRight rightExit

/-- A state whose decision is not internal is at an exit. -/
theorem stopping_means_exiting {state : source.Machine}
    (stopped : ∀ next, source.decide state ≠ .internal next) :
    ∃ exitState, source.decide state = .exit exitState := by
  match decision : source.decide state with
  | .internal next => exact absurd decision (stopped next)
  | .exit exitState => exact ⟨exitState, rfl⟩

end SerialFunctionSource

/-! ## The behaviour an implementation selects -/

/--
**The behaviour an implementation actually selects.**

`agent-bus` `g-design:141`, ruling on `g-auditor:12`. The gap it closes: with
`converse` stated between a source and the *contract*, every public `Post` came
out single-valued — `post_is_determined` — and a public contract has no business
being that. A caller quantifies over what a call is *permitted* to do; only the
implementation knows what it *does*.

So the exactness moves here. `exitOf` and `after` are **functions**, which is
what "exact" means at this layer: given the input and the before-state, the
implementation reaches one exit and one after-state. A relation that admitted two
would not be a selection.

**And this is where the frontier refusal now lives.** A `blockingRead` whose
answer depends on how many bytes arrived is not a function of `(input, before)`
at all, so it has no `ExactSerialBehavior` — which is the same refusal
`a_call_that_can_answer_two_ways_is_not_serial` made before, moved to the layer
that can carry it without forcing every contract to be deterministic. §3's "a
synchronous platform API is still modeled by a child protocol because its return
is external entropy" is unchanged.
-/
structure ExactSerialBehavior {State : Type w} (contract : SerialFunctionContract State) :
    Type w where
  /-- Which exit this call takes. -/
  exitOf : contract.Input → State → contract.ExitState
  /-- And the state it leaves behind. -/
  after : contract.Input → State → State

/--
**The exact behaviour is one the contract permits.**

The refinement half of `g-design:141`'s two layers, and the only thing a caller
needs in order to reason from the contract about a real implementation: whatever
the implementation selects is inside what the contract allows.

It is deliberately one-directional. The contract may permit outcomes this
implementation never produces — that is what makes it a *public* contract — and
nothing here forces it not to.
-/
def ExactSerialBehavior.Refines {State : Type w} {contract : SerialFunctionContract State}
    (behavior : ExactSerialBehavior contract) : Prop :=
  ∀ input before, contract.Pre input before →
    contract.Post input (behavior.exitOf input before) before (behavior.after input before)


/-! ## Relating a source to its contract -/

/--
The conformance §3 calls `FiniteStutteringCallSimulation`, at the fields this
layer can state.

**§3's `converse` is deliberately not a field here**, and `agent-bus`
`g-design:141` is why. Stated between a source and the *contract*, it forces
every public `Post` to be single-valued: a `Post` admitting two after-states for
one call would need the machine to reach both, and `exit_is_unique` says it
reaches one. A public contract has no business being deterministic, because a
caller quantifies over what a call is *permitted* to do. `converse` relates a
source to an `ExactSerialBehavior` instead, in `SerialFunctionRealizesExactly`,
and a caller reads the contract through `ExactSerialBehavior.Refines`.
-/
structure SerialFunctionRealizes {State : Type w}
    (contract : SerialFunctionContract State)
    (source : SerialFunctionSource contract) : Prop where
  /--
  **§3's `exit`: every machine exit is a contract exit, at the state it reads.**
  -/
  exitsPost : ∀ input before finish exitState, contract.Pre input before →
    source.InternalSteps (source.enter input before) finish →
    source.decide finish = .exit exitState →
    contract.Post input exitState before (source.read finish)
  /--
  **§3's `bounded`: a claimed work bound is met.**

  What makes `Responsive` a proof rather than a number the author wrote. §3:
  "If a product responsiveness theorem needs a numeric amount of work between
  frontiers, `workBound` is present *and proved*".
  -/
  bounded : ∀ bound, contract.workBound = some bound →
    ∀ input before, contract.Pre input before →
      ∃ finish, source.InternalStepsWithin (bound input before)
        (source.enter input before) finish ∧ (source.decide finish).IsExit

namespace SerialFunctionRealizes

variable {State : Type w} {contract : SerialFunctionContract State}
  {source : SerialFunctionSource contract}

/-- **And a claimed responsiveness bound is met by the machine.** -/
theorem responsive_is_realized (realizes : SerialFunctionRealizes contract source)
    (responsive : contract.Responsive)
    {input : contract.Input} {before : State} (pre : contract.Pre input before) :
    ∃ bound finish, contract.workBound = some bound ∧
      source.InternalStepsWithin (bound input before)
        (source.enter input before) finish ∧ (source.decide finish).IsExit := by
  obtain ⟨bound, isSome⟩ := responsive
  obtain ⟨finish, steps, isExit⟩ := realizes.bounded bound isSome input before pre
  exact ⟨bound, finish, isSome, steps, isExit⟩

end SerialFunctionRealizes

/-! ## Relating a source to the behaviour it selects -/

/--
**The machine does exactly what the implementation selected.**

Where `agent-bus` `g-design:141` puts `converse`. Both directions are here and
both are about a *function*, so neither forces anything on the contract:
`onlyThatExit` says any exit the machine reaches is the selected one at the
selected state, and `converse` says the selected one is reached.

`exit_is_unique` already says a machine reaches at most one exit from an entry.
What this adds is that the one it reaches is the one the implementation chose,
which is the claim `CollapsesToOneTransition` needs and the claim a contract
should never have had to make.
-/
structure SerialFunctionRealizesExactly {State : Type w}
    {contract : SerialFunctionContract State}
    (behavior : ExactSerialBehavior contract)
    (source : SerialFunctionSource contract) : Prop where
  /--
  **Any exit the machine reaches is the selected one, at the selected state.**

  What `exit_and_answer_are_determined` used to be, at the layer that can carry
  it. That theorem concluded any two *permitted* answers to one call agree, which
  was true only because `converse` forced the contract single-valued — the defect
  `agent-bus` `g-design:141` corrects.

  This says nothing about what the contract permits and everything about what the
  implementation does. A `Post` relating one call to several after-states is left
  alone, and the ones the machine does not produce are permitted-but-unproduced,
  which is what a public contract is for.
  -/
  onlyThatExit : ∀ input before finish exitState, contract.Pre input before →
    source.InternalSteps (source.enter input before) finish →
    source.decide finish = .exit exitState →
    exitState = behavior.exitOf input before ∧
      source.read finish = behavior.after input before
  /-- And the selected one is reached. -/
  converse : ∀ input before, contract.Pre input before →
    ∃ finish, source.InternalSteps (source.enter input before) finish ∧
      source.decide finish = .exit (behavior.exitOf input before) ∧
      source.read finish = behavior.after input before

namespace SerialFunctionRealizesExactly

variable {State : Type w} {contract : SerialFunctionContract State}
  {behavior : ExactSerialBehavior contract} {source : SerialFunctionSource contract}

/--
**A source that realizes a refining behaviour realizes the contract.**

The direction a caller needs, and the only one. Every exit the machine reaches
is the selected one, and the selection is inside what the contract permits — so
every machine exit is a contract exit at the state it reads, which is
`SerialFunctionRealizes.exitsPost`.

The converse direction is deliberately absent: the contract may permit outcomes
this implementation never produces, and nothing here says otherwise.
-/
theorem exitsPost (exact : SerialFunctionRealizesExactly behavior source)
    (refines : behavior.Refines) :
    ∀ input before finish exitState, contract.Pre input before →
      source.InternalSteps (source.enter input before) finish →
      source.decide finish = .exit exitState →
      contract.Post input exitState before (source.read finish) := by
  intro input before finish exitState pre steps atExit
  obtain ⟨sameExit, sameState⟩ := exact.onlyThatExit input before finish exitState pre steps atExit
  rw [sameExit, sameState]
  exact refines input before pre

end SerialFunctionRealizesExactly

/-! ## When a collapse is permitted -/

/--
`docs/PROCESS.md` §3's `SerialCallVisibility`.

> Exclusive ownership makes every intermediate write private. A call touching
> shared state instead supplies a linearization point and a noninterference
> proof; a footprint alone is insufficient.

An inductive with two constructors rather than a side condition on the
footprint, because what the call changed and who could observe it mid-flight are
different questions and neither derives the other.

`Exclusive`, `LinearizesAt` and `Noninterference` are parameters supplied by the
surrounding plan: the same proved routine is exclusive in one network and needs
a linearization point in another. Nothing here ties `Exclusive` to
`footprintAgrees`, which §3 does — see the module note and
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.32.
-/
inductive SerialCallVisibility {State : Type w} (contract : SerialFunctionContract State)
    (Exclusive : contract.Input → State → Prop)
    (LinearizationPoint : Type w)
    (LinearizesAt : LinearizationPoint → contract.Input → State → Prop)
    (Noninterference : LinearizationPoint → contract.Input → State → Prop)
    (input : contract.Input) (before : State) : Type w
  /-- The caller owns everything the call touches, so no intermediate state is visible. -/
  | exclusive (owned : Exclusive input before)
  /-- Or it does not, and supplies a point and a noninterference argument. -/
  | linearized (point : LinearizationPoint)
      (atomic : LinearizesAt point input before)
      (noninterference : Noninterference point input before)

/--
**A serial call adds no demand occurrence and no observation.**

`docs/PROCESS.md` §3: "It does not create a child instance, channel, demand
occurrence, or scheduling point merely because the machine realization uses an
ABI `call`."

`sound` exhibits the zero-issuing step and `demandFree` bounds it. Both are
needed: `ProcessSpec.Step` is a relation, so a witness with `issued = 0` says
nothing about what else the same transition admits — an earlier version had only
`sound` and a docstring claiming the bound.

`source` and `realizes` are fields, not context. Without them the collapse
consults no frontier-freedom argument at all, which is what local adversarial
review found: `noFrontier` had been deleted from the contract and replaced by a
fact about a type no consumer had to inhabit.
-/
structure CollapsesToOneTransition {p : ProcessSpec.{u, w}}
    (contract : SerialFunctionContract p.State)
    (Exclusive : contract.Input → p.State → Prop)
    (LinearizationPoint : Type w)
    (LinearizesAt : LinearizationPoint → contract.Input → p.State → Prop)
    (Noninterference : LinearizationPoint → contract.Input → p.State → Prop)
    (event : ProcessEvent p.vocabulary) : Type (max u (w + 1)) where
  /-- The machine that realizes the contract. -/
  source : SerialFunctionSource contract
  /-- And the proof that it does — including §3's `converse`. -/
  realizes : SerialFunctionRealizes contract source
  /-- The behaviour the implementation selected. -/
  behavior : ExactSerialBehavior contract
  /-- Which the machine runs exactly. -/
  exact : SerialFunctionRealizesExactly behavior source
  /-- And which is inside what the contract permits. -/
  refines : behavior.Refines
  /-- Every permitted call is a step of the process, issuing nothing and emitting nothing. -/
  sound : ∀ input exit before after, contract.Pre input before →
    contract.Post input exit before after → p.Step before event after 0 []
  /-- **And no other bag or segment is admitted at that transition.** -/
  demandFree : ∀ input exit before after issued emitted, contract.Pre input before →
    contract.Post input exit before after →
    p.Step before event after issued emitted → issued = 0 ∧ emitted = []
  /-- And every call at a permitted entry has a visibility witness. -/
  visibility : ∀ input before, contract.Pre input before →
    SerialCallVisibility contract Exclusive LinearizationPoint LinearizesAt
      Noninterference input before

namespace CollapsesToOneTransition

variable {p : ProcessSpec.{u, w}} {contract : SerialFunctionContract p.State}
  {Exclusive : contract.Input → p.State → Prop} {LinearizationPoint : Type w}
  {LinearizesAt : LinearizationPoint → contract.Input → p.State → Prop}
  {Noninterference : LinearizationPoint → contract.Input → p.State → Prop}
  {event : ProcessEvent p.vocabulary}

/--
**So the transition issues nothing, whatever witness one has of it.**

The bound rather than the witness: any `Step` at this transition has an empty
bag and an empty segment, so a run's outstanding demands really are unchanged by
the call.
-/
theorem issues_nothing
    (collapse : CollapsesToOneTransition contract Exclusive LinearizationPoint
      LinearizesAt Noninterference event)
    {input : contract.Input} {exit : contract.ExitState}
    {before after : p.State} {issued : Bag p.Demand}
    {emitted : ObservationSegment p.Observation}
    (pre : contract.Pre input before) (post : contract.Post input exit before after)
    (step : p.Step before event after issued emitted) : issued = 0 ∧ emitted = [] :=
  collapse.demandFree input exit before after issued emitted pre post step

/--
**And the call runs one answer**, because a collapse carries the behaviour its
machine selects.

The consequence of making `behavior`, `exact` and `refines` fields: a caller who
has a collapse has the frontier-freedom argument rather than having to trust that
somebody checked one elsewhere.

Note what it does *not* say, since the earlier version did and was wrong to. It
does not say the contract's `Post` is single-valued. A `Post` may permit answers
this machine never produces; what a collapse rules out is the machine producing
an answer nobody selected, which is where external entropy would have to enter.
`agent-bus` `g-design:141`.
-/
theorem answer_is_the_selection
    (collapse : CollapsesToOneTransition contract Exclusive LinearizationPoint
      LinearizesAt Noninterference event)
    {input : contract.Input} {before : p.State} {finish : collapse.source.Machine}
    {exitState : contract.ExitState} (pre : contract.Pre input before)
    (steps : collapse.source.InternalSteps (collapse.source.enter input before) finish)
    (atExit : collapse.source.decide finish = .exit exitState) :
    exitState = collapse.behavior.exitOf input before ∧
      collapse.source.read finish = collapse.behavior.after input before :=
  collapse.exact.onlyThatExit input before finish exitState pre steps atExit

/--
A collapse names its visibility.

A projection, and stated because §3 requires the field: there is no collapse
whose visibility went unstated. It does *not* say that some call has no
visibility witness — `Exclusive` is the plan's to choose, and a plan that chose
`fun _ _ => True` would satisfy it everywhere. That is §10.32.
-/
def collapse_names_its_visibility
    (collapse : CollapsesToOneTransition contract Exclusive LinearizationPoint
      LinearizesAt Noninterference event)
    (input : contract.Input) (before : p.State)
    (pre : contract.Pre input before) :
    SerialCallVisibility contract Exclusive LinearizationPoint LinearizesAt
      Noninterference input before :=
  collapse.visibility input before pre

end CollapsesToOneTransition

end Grass.Process
