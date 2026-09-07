import Grass.Process.Spec

/-!
# What a specification accepts

`docs/PROCESS.md` §4 gives `ProcessCorrect` fields whose types mention
`TerminalAccepts`, `TraceAccepts`, `DemandsWellFormed`, and
`OptionalViewAccepts`. Those are *acceptance* relations, and a bare
`ProcessSpec` carries none of them: it is a state machine, not a claim about
which behaviors are wanted.

Inventing acceptance here would build a second observation oracle beside
`docs/SEMANTICS.md`'s, which `docs/FOUNDATION.md` law 11 forbids ("semantic
facts have narrow owners and consumers use their exported theorems"). So this
module declares the *shape* of the acceptance data a process correctness proof
consumes, and leaves its construction to whoever owns the specification:

- `Grass.Semantics` derives one from a `BehaviorContract` when it lands;
- a standalone protocol in `Grass.Std.Process` supplies one directly, because
  its contract is its own;
- `Grass.Process.Weave` composes them across a plan.

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.2 records this as a decision, and §10.2
records the dependency cycle between this layer and `Grass.Semantics` that makes
it necessary rather than merely tidy.

## These predicates are trusted specification input, and that is a boundary

**Every field of `ProcessAcceptance` is an author-supplied `Prop`, and nothing
here or anywhere else checks that it says something.** `agent-bus` ruling
`g-design:84` on `c-process:69` settles this, and settles it against adding a
mechanism: any author-supplied `Prop` can intentionally be tautological, and Lean
cannot distinguish one that is from one that happens to hold. So the honest
statement is the boundary rather than a field that would pretend to police it.

`docs/FOUNDATION.md` law 15 is where the boundary already lives — "presentations
and realizations remain reviewed replaceable inputs". An acceptance is not
program meaning; it is a *claim about* program meaning, and it is trusted in the
same sense and reviewed in the same way.

Three consequences worth stating rather than leaving implicit:

* **Prefer derivation.** An acceptance derived from the precious
  `BehaviorContract` inherits that contract's review. That is the intended
  route, and `Grass.Semantics` is expected to supply it.
* **A standalone protocol library supplying one directly is asserting it**, and
  therefore requires adequacy review of the acceptance itself, not only of the
  process that satisfies it.
* **A fixture showing that *this* acceptance rejects a wrong value is evidence
  about that acceptance, and is not a general non-vacuity guarantee.**
  `Tests/Process/ViewFixtures.lean`'s
  `a_view_that_disagrees_with_the_state_is_refused` is exactly such a fixture and
  says exactly that much.

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.102 records how this was found: giving
`ViewAccepts` the state made a real obligation *possible* and did not make a
vacuous one impossible, and the render-graph predicate — `fun facet state view =>
view = facet.render state` — discharges `ProcessCorrect.viewAccepts` by `rw` for
every specification while passing the single-valuedness test used elsewhere in
this codebase.

## The terminal-remainder law arrives here

`terminalRemainder` is the law `docs/PROCESS.md` §2 calls "the specification's
progress/lifecycle law". It is a field of the acceptance rather than of the
`ProcessSpec` because §3 is explicit that a lifecycle promise is a facet
attached where it is exported, and that "uncancellable leaf processes gain no
new author obligation". A leaf protocol author writes a `ProcessSpec` and
nothing else; whoever owns the specification supplies the law along with the
rest of what it accepts. `Grass/Process/Spec.lean` records the withdrawal of the
earlier design that made it a mandatory spec field.

## Traces here are prefixes

`TraceAccepts` ranges over the history of a finite execution prefix, not over
the limit trace of a maximal run. That is deliberate and it is a restriction on
what this field can express: it can carry a safety property ("no byte is written
before the header"), and it does not by itself carry a liveness property ("the
response is eventually written"). Liveness for this layer is
`Grass/Process/Progress.lean` plus, at the network level, the adequacy theorem.
`docs/PROCESS.md` §7 draws the same line: "Universal prefix safety quantifies
over that model. Conditional responsiveness is separate."
-/

namespace Grass.Process

universe u w

/--
The acceptance data a `ProcessCorrect` proof is stated against.

Every field is supplied by the owner of the specification, never derived here.
-/
structure ProcessAcceptance (p : ProcessSpec.{u, w}) where
  /-- Which terminal results this request may legitimately finish with. -/
  TerminalAccepts : p.Request → p.TerminalResult → Prop
  /--
  Which observation prefixes are acceptable. See the module note: this is a
  prefix property, so it expresses safety and not liveness.
  -/
  TraceAccepts : Trace p.Observation → Prop
  /--
  Which demand bags are well formed.

  `docs/PROCESS.md` §4 has this as a separate obligation from the invariant
  because a specification can constrain what may be *asked for* — at most one
  outstanding write per handle, no read while draining — independently of what
  the state looks like.
  -/
  DemandsWellFormed : Bag p.Demand → Prop
  /--
  **Which rendered views are acceptable, at which states.**

  The state argument is what makes this an obligation. Without it the clause sees
  a facet and a value and nothing else, so it cannot say the view *reflects*
  anything — and `ProcessCorrect.viewAccepts` is handed exactly
  `ViewAccepts facet (facet.render state)`, which any predicate satisfied by the
  render's own image discharges for free.

  Two rounds of local adversarial review made that concrete.
  `Tests/Process/ViewFixtures.lean` first closed §10.56 with the image of the
  render, and a reviewer discharged the obligation at a facet the specification
  does not carry. It was replaced with a *bound*, and a second reviewer mutated
  the render to a constant and watched the bound survive: a view reporting "no
  work remains" at a working state was accepted, because nothing in the clause
  could see the state to disagree with.

  With the state here, an acceptance names the projection it intends and the
  process has to implement it. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.99.

  **That made a real obligation possible and did not make a vacuous one
  impossible**, which §10.102 records and `g-design:84` ruled on. The render
  graph — `fun facet state view => view = facet.render state` — still discharges
  `ProcessCorrect.viewAccepts` for every specification, facet and render, and no
  field of this record can refuse it. See the module note on the trust boundary:
  this predicate is specification input under `docs/FOUNDATION.md` law 15, and
  the fixtures show what a *particular* acceptance refuses rather than that any
  acceptance refuses anything.
  -/
  ViewAccepts : (facet : ViewFacet p.State) → p.State → facet.View → Prop
  /--
  Which observations the specification *demands*, as opposed to merely permits.

  This is the third disjunct of `docs/PROCESS.md` §7 progress: a cycle is
  progressing if it produces "an independently specified observation". That
  phrase is specification-relative — an observation the specification did not
  ask for is not intended to discharge a progress obligation, or every process
  could satisfy progress by logging — so the predicate has to come from here and
  not from the process.
  -/
  Demanded : p.Observation → Prop
  /--
  How a terminating run may dispose of the demands still outstanding.

  See the module note. `TerminalRemainderLaw.strict` is the right default; a
  specification with no lifecycle constraint says so with `unconstrained`, which
  a reviewer can see.
  -/
  terminalRemainder : TerminalRemainderLaw p

namespace ProcessAcceptance

variable {p : ProcessSpec.{u, w}}

/--
A segment counts toward progress when it contains an observation the
specification demanded.
-/
def SegmentIsDemanded (accept : ProcessAcceptance p) (segment : p.Segment) : Prop :=
  ∃ observation ∈ segment, accept.Demanded observation

theorem not_segmentIsDemanded_nil (accept : ProcessAcceptance p) :
    ¬ accept.SegmentIsDemanded [] := by
  rintro ⟨observation, member, _⟩
  exact absurd member List.not_mem_nil

/--
The acceptance that constrains nothing.

Useful for a process whose correctness is entirely carried by its invariant, and
useful as an honest marker: a proof built against `trivial` has proved that the
machine does what it does, not that what it does is wanted.

Two fields are deliberately *not* trivial in the permissive direction.
`Demanded` is `fun _ => False`, so this acceptance cannot discharge a progress
obligation by emitting anything at all. `terminalRemainder` is `unconstrained`
rather than `strict`, because a marker for "nothing is checked" should not
quietly impose the strongest lifecycle law; a reviewer seeing `trivial` should
read it as no custody claim being checked.
-/
def trivial (p : ProcessSpec.{u, w}) : ProcessAcceptance p where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  DemandsWellFormed := fun _ => True
  ViewAccepts := fun _ _ _ => True
  Demanded := fun _ => False
  terminalRemainder := TerminalRemainderLaw.unconstrained p

theorem trivial_demands_nothing (p : ProcessSpec.{u, w}) (segment : p.Segment) :
    ¬ (trivial p).SegmentIsDemanded segment := by
  rintro ⟨_, _, demanded⟩
  exact demanded

end ProcessAcceptance

end Grass.Process
