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

## `noFrontier` is structural, not a field

§3's `SerialFunctionContract` ends with `noFrontier :
NoExternalPendingCancellationOrInterleavingFrontier`, and there is no such
field here. It would be an opaque promise: an author writes `noFrontier := ⟨⟩`
and nothing checks it, which is the shape `docs/DECISIONS.md` decision 131
rejected for `ChannelContract`.

Instead `SerialDecision` has two constructors where
`Grass/Process/Sequential/Machine.lean`'s `SequentialDecision` has three. A
sequential machine may decide `.effect demand resume` — ask the environment and
wait. A serial function has no such constructor, so "waits for external entropy"
is not a thing it can do; `no_waiting_decision` is that, by cases.

The consequence is the one §3 wants and it is stronger than the sequential
analogue. `SequentialMachine.reachesFrontier` proves finitely many internal
steps reach an effect *or* a terminal. `reaches_an_exit` here proves they reach
an **exit** — there is no other kind of stopping place — which is §3's
`EveryMaximalInternalExecutionHasExactlyOneDeclaredExit`.

## What is still a field, and why

`Post`, `obligations`, `resources`, and `faultCustody` stay fields: they are the
content of the contract and nothing structural can supply them. `footprint` is
carried as an agreement relation rather than as an opaque `LogicalFootprint`, so
`postWithinFootprint` is a claim about a value the author supplied — the same
trade as `NetworkAssertion.framed`.

`workBound` stays an `Option`, and `terminating_is_not_bounded` is why: §3 says
"If a product responsiveness theorem needs a numeric amount of work between
frontiers, `workBound` is present and proved; bare termination is not silently
promoted to a latency bound." A contract with a well-founded rank and
`workBound = none` terminates and bounds nothing, and `Responsive` is the
predicate a consumer has to ask for rather than assume.

## What this module does not do

It does not prove `FiniteStutteringCallSimulation`: relating a contract to a
*machine* realization is `docs/MACHINE.md`'s layer, not this one, and
`Grass.Process` has no machine. `SerialCallVisibility` is here because it is the
condition under which a collapse is *permitted*, and §3 is explicit that "a
footprint alone is insufficient" — so the visibility witness has to exist as a
type before anything can require it.
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
`.effect demand resume`, and its absence is §3's `noFrontier` — not as a promise
an author makes but as a decision they cannot express.
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
**No decision waits.**

`docs/PROCESS.md` §3's `NoExternalPendingCancellationOrInterleavingFrontier`, as
a fact about the type rather than a field of the contract. Every decision either
continues internally or exits, so "remain pending" is not something a serial
function can decide to do.

Compare `Grass/Process/Sequential/Machine.lean`'s `SequentialDecision.AtFrontier`,
which is *true* of `.effect` — a sequential machine can wait, and a serial
function cannot. That is the semantic boundary §3 draws, and it is drawn by the
constructor list rather than by an obligation.
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

Three deliberate departures from the declaration, all recorded in the module
note: `noFrontier` is structural rather than a field, `footprint` is an
agreement relation rather than an opaque `LogicalFootprint`, and
`FiniteStutteringCallSimulation` is absent because this layer has no machine.
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
  /-- When it may be called. -/
  Pre : Input → State → Prop
  /-- What each exit means. -/
  disposition : ExitState → SerialCallDisposition Output Fault
  /-- The state transformation each exit performs. -/
  Post : Input → ExitState → State → State → Prop
  /--
  Two states agree outside what this call may touch.

  §3's `footprint : LogicalFootprint`, carried as the relation a footprint
  *induces* rather than as an opaque handle. That is what makes
  `postWithinFootprint` checkable: an author who declares a narrow footprint and
  writes a `Post` that changes more cannot discharge it.
  -/
  footprintAgrees : State → State → Prop
  /-- **And the call really stays inside it.** -/
  postWithinFootprint : ∀ input exit before after,
    Post input exit before after → footprintAgrees before after
  /-- What each exit does to local obligations. -/
  Obligations : Type w
  /-- Its obligation transformation. -/
  obligations : Input → ExitState → Obligations → Obligations → Prop
  /-- What each exit does to local resources. -/
  Resources : Type w
  /-- Its resource transformation. -/
  resources : Input → ExitState → Resources → Resources → Prop
  /-- The mutation and custody a raised fault leaves behind. -/
  faultCustody : Fault → State → State → Prop
  /--
  **A raised fault declares its exact partial mutation.**

  §3: "Each exit fixes the logical post-state, resource custody, obligation
  custody, and any partial mutation; there is no generic exceptional edge whose
  state is left implicit."
  -/
  faultsDeclared : ∀ input exit before after fault,
    disposition exit = .raised fault → Post input exit before after →
    faultCustody fault before after
  /-- The carrier of the internal measure. -/
  Rank : Type w
  /-- Its strict order. -/
  rankLt : Rank → Rank → Prop
  /-- No infinite internal descent. -/
  rankWellFounded : WellFounded rankLt
  /--
  A numeric work bound, when a product responsiveness theorem needs one.

  §3: "bare termination is not silently promoted to a latency bound." `none` is
  the ordinary case and `Responsive` below is what a consumer must ask for.
  -/
  workBound : Option (Input → State → Nat)

namespace SerialFunctionContract

variable {State : Type w} (contract : SerialFunctionContract State)

/--
The contract claims a numeric work bound.

Stated as a predicate rather than read off the `Option` at each use site,
because §3's point is that a consumer has to *ask*: a contract that terminates
is not thereby responsive.
-/
def Responsive : Prop := ∃ bound, contract.workBound = some bound

/--
**Termination does not give a work bound.**

The `Option` is doing real work: a contract carries a well-founded rank
unconditionally and a numeric bound only when someone proved one, so a
responsiveness theorem cannot be assembled out of termination alone. Stated as
the obvious fact that `none` is not `some`, because the alternative — a
`workBound : Input → State → Nat` field — would have made every terminating
contract claim a latency bound it had not proved.
-/
theorem terminating_is_not_bounded (noBound : contract.workBound = none) :
    ¬ contract.Responsive := by
  rintro ⟨bound, isSome⟩
  rw [noBound] at isSome
  exact absurd isSome (by simp)

/-! ### Exits -/

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

/-- **And a raising exit's mutation is declared.** -/
theorem raising_exit_declares_its_mutation {exit : contract.ExitState}
    (raises : Raises exit) {input : contract.Input} {before after : State}
    (post : contract.Post input exit before after) :
    ∃ fault, contract.faultCustody fault before after := by
  obtain ⟨fault, isRaised⟩ := raises
  exact ⟨fault, contract.faultsDeclared input exit before after fault isRaised post⟩

/-- **And every exit stays inside the footprint, raising or returning alike.** -/
theorem every_exit_stays_inside_the_footprint {input : contract.Input}
    {exit : contract.ExitState} {before after : State}
    (post : contract.Post input exit before after) :
    contract.footprintAgrees before after :=
  contract.postWithinFootprint input exit before after post

end SerialFunctionContract

/-! ## A function as a machine, and the theorem that buys -/

/--
A serial function's internal structure: states, a decision at each, and a rank
its internal decisions decrease.

Separate from the contract because the contract is what a *caller* sees and this
is what an *author* writes. `reaches_an_exit` is what relates them.
-/
structure SerialFunctionSource {State : Type w}
    (contract : SerialFunctionContract State) : Type (w + 1) where
  /-- The function's own working state. -/
  Machine : Type w
  /-- Where it starts. -/
  enter : contract.Input → State → Machine
  /-- What it does at a state. -/
  decide : Machine → SerialDecision Machine contract.ExitState
  /-- Its internal measure. -/
  rank : Machine → contract.Rank
  /--
  **Internal decisions strictly decrease it.**

  The whole of an author's progress obligation, and `reaches_an_exit` is what it
  buys. §3's `EveryInternalAndRecursiveSCCEdgeStrictlyDecreases` covers ordinary
  CFG edges and recursive call edges alike, which is why the measure is on the
  machine state rather than on a syntactic position.
  -/
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

/--
**Every maximal internal execution reaches an exit.**

`docs/PROCESS.md` §3's `EveryMaximalInternalExecutionHasExactlyOneDeclaredExit`,
and the theorem that licenses collapsing a call into one process transition.

Compare `Grass/Process/Sequential/Machine.lean`'s `reachesFrontier`, which is
the same induction over the same kind of rank and reaches a weaker conclusion —
an effect *or* a terminal. The difference is entirely the constructor list: a
serial function cannot decide `.effect`, so there is no frontier for it to stop
at and "reaches a frontier" collapses into "exits".

That is what §3 means by the boundary being semantic. A computation that can
wait is not made serial by proving something about it; it fails to be
expressible as a `SerialFunctionSource` at all.
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

/--
And the exit it reaches is the only kind of stopping place there is.

Stated because the sequential analogue needs the reader to check *which*
frontier was reached; here there is nothing to check.
-/
theorem stopping_means_exiting {state : source.Machine}
    (stopped : ∀ next, source.decide state ≠ .internal next) :
    ∃ exitState, source.decide state = .exit exitState := by
  match decision : source.decide state with
  | .internal next => exact absurd decision (stopped next)
  | .exit exitState => exact ⟨exitState, rfl⟩

end SerialFunctionSource

/-! ## When a collapse is permitted -/

/--
`docs/PROCESS.md` §3's `SerialCallVisibility`.

> Exclusive ownership makes every intermediate write private. A call touching
> shared state instead supplies a linearization point and a noninterference
> proof; a footprint alone is insufficient.

The last clause is why this is an inductive with two constructors rather than a
side condition on the footprint. A contract's `footprintAgrees` says what the
call changed; it says nothing about who else could observe the change while it
was in progress, and there is no way to derive the second from the first.

`Interference` is a parameter rather than a field because what counts as
interference is a fact about the surrounding network, not about the function:
the same proved routine is exclusive in one plan and needs a linearization point
in another.
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

Written into the shape of the definition rather than proved about it: the issued
bag is `0` and the observation segment is `[]`, so a step that *did* issue
something is not a `CollapsesToOneTransition` at all. That is the same trade as
`NetworkAssertion.footprint` — an author supplies a value the type constrains,
instead of a promise a theorem restates.

`visibility` is a field because §3 requires it and because a collapse without
one would be `docs/FOUNDATION.md` law 8's permissive fallback: the ordinary case
would silently become the exclusive case.
-/
structure CollapsesToOneTransition {p : ProcessSpec.{u, w}}
    (contract : SerialFunctionContract p.State)
    (Exclusive : contract.Input → p.State → Prop)
    (LinearizationPoint : Type w)
    (LinearizesAt : LinearizationPoint → contract.Input → p.State → Prop)
    (Noninterference : LinearizationPoint → contract.Input → p.State → Prop)
    (event : ProcessEvent p.vocabulary) : Type (max u (w + 1)) where
  /-- Every permitted call is a step of the process, issuing nothing and emitting nothing. -/
  sound : ∀ input exit before after, contract.Pre input before →
    contract.Post input exit before after → p.Step before event after 0 []
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
**So the process's outstanding demands are unchanged by the call.**

The consequence a caller wants: a transition realized by a serial call
contributes nothing to the run's outstanding bag, which is why the call needs no
occurrence identity, no child, and no escrow.
-/
theorem issues_nothing
    (collapse : CollapsesToOneTransition contract Exclusive LinearizationPoint
      LinearizesAt Noninterference event)
    {input : contract.Input} {exit : contract.ExitState} {before after : p.State}
    (pre : contract.Pre input before) (post : contract.Post input exit before after) :
    p.Step before event after 0 [] :=
  collapse.sound input exit before after pre post

/--
**And a collapse cannot be had without saying why it is invisible.**

`docs/FOUNDATION.md` law 8 at this seam: there is no default. A call that
neither owns what it touches nor supplies a linearization point has no
visibility witness, so it has no `CollapsesToOneTransition` and stays a frontier.
-/
theorem collapse_names_its_visibility
    (collapse : CollapsesToOneTransition contract Exclusive LinearizationPoint
      LinearizesAt Noninterference event)
    (input : contract.Input) (before : p.State) (pre : contract.Pre input before) :
    Nonempty (SerialCallVisibility contract Exclusive LinearizationPoint LinearizesAt
      Noninterference input before) :=
  ⟨collapse.visibility input before pre⟩

end CollapsesToOneTransition

end Grass.Process
