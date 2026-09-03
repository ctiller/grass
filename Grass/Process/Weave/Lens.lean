import Grass.Process.Weave.Mixin

/-!
# Refinement lenses: replacing one subgraph without reopening the others

`docs/PROCESS.md` §8:

> Refinement itself is local. A `ProcessRefinementLens` selects one abstract
> role or subgraph and its complete typed boundary. Replacing it preserves
> observation origin, channel order, linear/shared custody, obligations,
> resource flux, and progress at that boundary while introducing a finite
> requirement delta. The generic contextual theorem frames every nonselected
> process. Thus one proof may replace only the graphics role with Vulkan
> protocols while leaving disk I/O abstract; a later proof may replace only disk
> I/O with Win32 asynchronous-file and IOCP protocols. Neither reopens the
> other's internal proof.

The claim with teeth there is the last two sentences, and this module proves
them. Everything else in the paragraph is a list of things a *replacement* must
preserve — a simulation obligation between two plans, which needs a refinement
relation this layer does not have — and those are named rather than quietly
skipped.

## The contextual theorem costs nothing new

`frames_every_exterior_mixin` is §8's "generic contextual theorem", and its
proof is one application of `WeaveInvariantMixin.frames_past_unrelated_steps`.
That is the argument for the scope discipline rather than a shortcoming of this
module: an assertion carries a footprint, a transition carries a scope, a lens
carries an interior, and "a step inside the lens cannot disturb an invariant
outside it" is what those three compose to.

`disjoint_lenses_do_not_reopen_each_other` is the same fact between two lenses,
which is §8's graphics-and-disk sentence. Neither refinement's author knows the
other exists.

## What a lens must include to be worth anything

A lens whose interior excludes the observation trace selects **no emitting
step** — `emitting_steps_need_the_trace_inside`. That is not a defect to route
around; it is the honest statement of a real constraint, and it is why §8 lists
"observation origin" first among the things a replacement must preserve. A
refinement of a subgraph that emits has the trace in its interior, so an
exterior invariant about the trace is *not* framed for free and the refinement
owes the origin-preservation obligation instead.

The same shape appears in `Grass/Process/Trace/Linearization.lean`: two
independent steps never both emit, because the trace is one fragment. Two
disjoint lenses likewise cannot both contain it, so at most one refinement in a
weave may change what the program observes without an explicit argument.

## What `Disjoint` does not separate

Two disjoint lenses can still interfere through fragments neither declares.
When this module was written that was not hypothetical: no constructor of
`NetworkTransition` named `.obligations` or `.session` in its scope at all, so a
mixin about either framed past every step in the program, vacuously. Both are
fixed — `Delivers`, `ClosesSession` and `KillsSession` move the session,
`EndsInstance` moves the ledger — and `docs/PROCESS_IMPLEMENTATION_PLAN.md`
§10.28 records what remains.

What still is not separated: `Disjoint` is disjointness of *interiors*, and a
channel between a selected and an unselected role is achieved by one lens taking
the shared boundary outright rather than by there being no shared boundary. A
listener mixin about the listener's own channel behaviour is excluded from
`disjoint_lenses_do_not_reopen_each_other` for that reason.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

namespace ProcessPlan

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {Obligations : Type o} {plan : ProcessPlan.{u, w, v, r, m, o} registry boundary Obligations}

/--
The part of a network one refinement replaces.

`Selected` names the roles; `Interior` names the fragments they own. Both are
needed and neither determines the other: a role owns its own instance state, but
whether it owns a shared region or the observation trace is a fact about the
graph, not about the role's name.

Four coupling fields stop `Interior` being chosen to suit the theorem, and it
is worth being precise about what each one rules out, because a first draft had
only the first two and local adversarial review walked straight through the gap.

* `selectedStateInterior` forbids a lens that claims a role and disowns its
  state.
* `unselectedStateExterior` forbids claiming an *unselected role's private
  state* — and nothing else. On its own it permitted a lens that owned the
  shared region only an unselected role was declared against, the global nominal
  history, the observation trace, and every channel's escrow including channels
  between two roles it did not select. Two of those four are now closed by the
  fields below; **the nominal history and the observation trace are not**, so a
  lens may still claim either, and `unselected_state_is_untouched` is
  correspondingly narrow — it guarantees an unselected role its private slot and
  nothing else.
* `interiorChannelsTouchTheSelection` closes the escrow half: a channel is
  interior only if the lens selected one of its endpoints. Without it a lens
  with `Selected := fun _ => False` could still select real channel steps, which
  makes "one abstract role or subgraph" a docstring rather than a type.
* `interiorRegionsAreWritable` closes the shared-state half, using the
  capability the graph already declares: a region is interior only if some
  selected role may write it.

**What remains open, disclosed rather than hidden.** `Selects` is still a
predicate on a transition's *scope*, and `NetworkTransition`'s twelve channel
constructors carry an edge and a session but never the role that took the step.
So a lens selecting one endpoint of a channel may select steps the *other*
endpoint took on it. Closing that needs the transition family to attribute
channel steps to endpoints, which is `Grass/Process/Network/Transition.lean`'s
change and is recorded in `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.29.
-/
structure ProcessRefinementLens where
  /-- The roles this refinement replaces. -/
  Selected : plan.topology.ProcessKind → Prop
  /-- The fragments it owns. -/
  Interior : plan.NetworkScope
  /-- A selected role's own state is interior. -/
  selectedStateInterior : ∀ kind slot, Selected kind → Interior (.instanceState kind slot)
  /-- And an unselected role's is not. -/
  unselectedStateExterior : ∀ kind slot, ¬ Selected kind → ¬ Interior (.instanceState kind slot)
  /--
  **An interior channel has a selected endpoint.**

  `docs/PROCESS.md` §8's "one abstract role or subgraph *and its complete typed
  boundary*", at the half a fragment predicate can express. A lens that owned a
  channel between two roles it did not select would be selecting steps of a
  subgraph it never named.
  -/
  interiorChannelsTouchTheSelection : ∀ edge session,
    Interior (.escrow edge session) →
    Selected (plan.topology.endpoints edge).1 ∨ Selected (plan.topology.endpoints edge).2
  /--
  **And an interior region is one a selected role may write.**

  Spending the capability `ProcessGraph.sharedAccess` already declares. A lens
  cannot claim a region that only unselected roles write, nor one that is
  read-only for everybody — which is exactly the fragment
  `Tests/Process/WeaveFixtures.lean` builds its immutability mixin around.
  -/
  interiorRegionsAreWritable : ∀ region, Interior (.region region) →
    ∃ kind, Selected kind ∧ (plan.topology.sharedAccess kind region).mayWrite = true
  /-- The requirements the network faces after this replacement. -/
  refinedRequirements : RequirementSet
  /--
  And the replacement only ever adds.

  `docs/PROCESS.md` §8: "Requirement deltas accumulate in the explicit
  `ProviderEnv`." A refinement that could *drop* a requirement would let a
  closure check pass because a frontier stopped being mentioned rather than
  because it was met.

  Named for the post-refinement total rather than for the delta, because that is
  what the law constrains: `RequirementSet` has no union, so "the delta" is not
  a value this layer can add to anything. Accumulating two independent
  refinements' deltas therefore has no statement here — see
  `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.30.
  -/
  refinementOnlyAdds : refinedRequirements.Covers boundary.requirements

namespace ProcessRefinementLens

variable (lens : plan.ProcessRefinementLens)

/-- A step of the selected subgraph: one whose whole scope is interior. -/
def Selects {before after : plan.LogicalProcessNetwork}
    (transition : plan.NetworkTransition before after) : Prop :=
  ∀ fragment, transition.scope fragment → lens.Interior fragment

/-- An invariant living outside the lens. -/
def Exterior (mixin : plan.WeaveInvariantMixin) : Prop :=
  ∀ fragment, mixin.Scope fragment → ¬ lens.Interior fragment

variable {lens}

/--
**The generic contextual theorem: a step inside the lens preserves every
invariant outside it.**

§8's "The generic contextual theorem frames every nonselected process", and the
whole of what makes local refinement local. The mixin's author never mentioned
the lens and the refinement's author never mentioned the mixin; the framing
comes from the mixin's footprint being inside its own scope, the step's changes
being inside its own scope, and the lens keeping those two apart.
-/
theorem frames_every_exterior_mixin {before after : plan.LogicalProcessNetwork}
    {mixin : plan.WeaveInvariantMixin} (exterior : lens.Exterior mixin)
    (step : plan.NetworkStep before after) (inside : lens.Selects step.transition)
    (held : mixin.assertion.holds before) : mixin.assertion.holds after :=
  mixin.frames_past_unrelated_steps step
    (fun fragment inStep inMixin => exterior fragment inMixin (inside fragment inStep)) held

/--
An execution every step of which is inside the lens.

Its own inductive rather than a `StepsTo` with a side condition, because the
side condition would have to be stated over *every* step of the plan — a
hypothesis so strong that only a lens containing the whole network could satisfy
it, which would make the theorem below say nothing. An earlier draft did exactly
that.
-/
inductive StepsInside (lens : plan.ProcessRefinementLens) :
    plan.LogicalProcessNetwork → plan.LogicalProcessNetwork → Prop
  /-- Zero steps. -/
  | still {network : plan.LogicalProcessNetwork} : StepsInside lens network network
  /-- One more, and it is inside. -/
  | more {first middle last : plan.LogicalProcessNetwork}
      (before : StepsInside lens first middle) (step : plan.NetworkStep middle last)
      (inside : lens.Selects step.transition) : StepsInside lens first last

/-- And across a whole execution of the selected subgraph. -/
theorem frames_along_an_interior_execution {before after : plan.LogicalProcessNetwork}
    {mixin : plan.WeaveInvariantMixin} (exterior : lens.Exterior mixin)
    (execution : StepsInside lens before after)
    (held : mixin.assertion.holds before) : mixin.assertion.holds after := by
  induction execution with
  | still => exact held
  | more _ step inside ih => exact frames_every_exterior_mixin exterior step inside ih

/-- An interior execution is an execution. -/
theorem StepsInside.toStepsTo {before after : plan.LogicalProcessNetwork}
    (execution : StepsInside lens before after) : plan.StepsTo before after := by
  induction execution with
  | still => exact .still
  | more _ step _ ih => exact .more ih step

/--
**An unselected role's state does not move under a step inside the lens.**

The concrete form of "frames every nonselected process": not merely that
invariants about it survive, but that its state is literally unchanged. This is
what lets a later refinement of *that* role start from the same state it would
have without this one.
-/
theorem unselected_state_is_untouched {before after : plan.LogicalProcessNetwork}
    (step : plan.NetworkStep before after) (inside : lens.Selects step.transition)
    (kind : plan.topology.ProcessKind) (slot : plan.topology.InstanceId kind)
    (unselected : ¬ lens.Selected kind) :
    before.instances kind slot = after.instances kind slot :=
  step.touchesOnly (.instanceState kind slot)
    (fun inStep => lens.unselectedStateExterior kind slot unselected (inside _ inStep))

/-! ## Two refinements that do not know about each other -/

/-- Two lenses select disjoint parts of the network. -/
def Disjoint (left right : plan.ProcessRefinementLens) : Prop :=
  ∀ fragment, left.Interior fragment → ¬ right.Interior fragment

theorem Disjoint.symm {left right : plan.ProcessRefinementLens}
    (disjoint : Disjoint left right) : Disjoint right left :=
  fun fragment inRight inLeft => disjoint fragment inLeft inRight

/--
**Neither refinement reopens the other's internal proof.**

§8's graphics-and-disk sentence, as a theorem: an invariant belonging entirely
to one lens survives every step of the other, and neither author wrote anything
about the other's existence.

Note what is *not* required — no ordering between the refinements, no
compatibility condition beyond disjointness of the fragments they own, and no
joint proof term. That is the difference between a weave of independently
certified mixins and one application-sized invariant.
-/
theorem disjoint_lenses_do_not_reopen_each_other
    {left right : plan.ProcessRefinementLens} (disjoint : Disjoint left right)
    {mixin : plan.WeaveInvariantMixin}
    (belongsToRight : ∀ fragment, mixin.Scope fragment → right.Interior fragment)
    {before after : plan.LogicalProcessNetwork} (step : plan.NetworkStep before after)
    (insideLeft : left.Selects step.transition)
    (held : mixin.assertion.holds before) : mixin.assertion.holds after :=
  frames_every_exterior_mixin
    (lens := left)
    (fun fragment inMixin inLeft => disjoint fragment inLeft (belongsToRight fragment inMixin))
    step insideLeft held

/-!
### Requirement accumulation across two lenses is not stated here

A first draft had a `deltas_accumulate` theorem whose conclusion was literally a
field of one of its arguments — `right.refinedRequirements.Covers
boundary.requirements` is `right.refinementOnlyAdds` — so both hypotheses were
discardable and it established no relation between two lenses at all.

The real statement needs a union of requirement sets, which
`Grass/Specification/Boundary.lean` does not provide: `RequirementSet` has
`Covers` and nothing that combines two sets. Recorded as owed rather than
approximated by a theorem that reads like it says something.
-/

/-! ## What a lens has to own to select anything -/

/--
**A lens whose interior excludes the observation trace selects no emitting
step.**

Not a defect to route around. It is why §8 lists "observation origin" first
among the things a replacement must preserve: a refinement of a subgraph that
emits *does* own the trace, so an exterior invariant about the trace is not
framed for free and the refinement owes an origin-preservation argument instead.

`Grass/Process/Trace/Linearization.lean` reaches the same shape from the other
side — two independent steps never both emit, because the trace is one fragment.
Two disjoint lenses likewise cannot both contain it.
-/
theorem emitting_steps_need_the_trace_inside {before after : plan.LogicalProcessNetwork}
    {transition : plan.NetworkTransition before after}
    (inside : lens.Selects transition) (emits : transition.scope .observations) :
    lens.Interior .observations :=
  inside .observations emits

/-- So two disjoint lenses cannot both own the trace, and at most one may emit. -/
theorem at_most_one_lens_may_emit
    {left right : plan.ProcessRefinementLens} (disjoint : Disjoint left right)
    {a b c d : plan.LogicalProcessNetwork}
    {leftStep : plan.NetworkTransition a b} {rightStep : plan.NetworkTransition c d}
    (insideLeft : left.Selects leftStep) (insideRight : right.Selects rightStep)
    (leftEmits : leftStep.scope .observations) : ¬ rightStep.scope .observations :=
  fun rightEmits =>
    disjoint .observations
      (emitting_steps_need_the_trace_inside insideLeft leftEmits)
      (emitting_steps_need_the_trace_inside insideRight rightEmits)

/-! ## The obligations a replacement still owes -/

/--
**A replacement may change only what the lens owns.**

The half of §8's preservation list this layer can state: whatever the
replacement does, every fragment outside the interior agrees before and after.
Stated over an arbitrary `Replacement` relation because the replacement is a
relation between two plans and this module has one plan — but it does mention
the lens, which is what makes it a constraint rather than relation implication
under a grand name. An earlier draft took two relations and said one implied the
other, mentioning neither the lens nor anything else.

`interior_steps_preserve_the_exterior` below discharges it for the case where
the replacement is a run of the selected subgraph, which is the only case this
layer has. A genuine cross-plan replacement is
`Grass/Process/Proof/Simulation.lean`'s.
-/
def PreservesTheExterior
    (Replacement : plan.LogicalProcessNetwork → plan.LogicalProcessNetwork → Prop) : Prop :=
  ∀ before after, Replacement before after →
    ∀ fragment, ¬ lens.Interior fragment →
      LogicalProcessNetworkCore.Agrees fragment before after

/--
**A run of the selected subgraph preserves the exterior.**

The obligation above discharged for the replacement this layer can express. Note
that it is stronger than `frames_every_exterior_mixin`: that one preserves
assertions, this one preserves the fragments themselves, so a later refinement
of an unselected role starts from exactly the state it would have without this
one.
-/
theorem interior_steps_preserve_the_exterior :
    lens.PreservesTheExterior (StepsInside lens) := by
  intro before after execution fragment outside
  induction execution with
  | still => exact LogicalProcessNetworkCore.agrees_refl fragment _
  | more _ step inside ih =>
    exact LogicalProcessNetworkCore.agrees_trans fragment _ _ _ ih
      (step.touchesOnly fragment (fun inStep => outside (inside fragment inStep)))

/-!
### And what none of this covers

"Observation origin, channel order, linear/shared custody, obligations,
resource flux, and progress **at that boundary**" are facts about the interior
being replaced, not about the exterior being framed, so `PreservesTheExterior`
says nothing about them. They are a relation between two plans and this module
has one plan; `Grass/Process/Proof/Simulation.lean` is where they belong.

Deliberately left as prose rather than as a named definition. Something of the
shape "there exists a witness that the boundary was preserved", written before
there is a refinement relation to witness it against, is satisfied by `True` and
would be worse than the omission it was meant to record.
-/

end ProcessRefinementLens

end ProcessPlan

end Grass.Process
