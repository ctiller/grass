import Grass.Process.Run

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

## Traces here are prefixes

`TraceAccepts` ranges over the history of a finite execution prefix, not over
the limit trace of a maximal run. That is deliberate and it is a restriction on
what this field can express: it can carry a safety property ("no byte is written
before the header"), and it cannot by itself carry a liveness property ("the
response is eventually written"). Liveness for this layer is
`Grass/Process/Progress.lean` plus, at the network level, the adequacy theorem.
`docs/PROCESS.md` §7 draws the same line: "Universal prefix safety quantifies
over that model. Conditional responsiveness is separate."
-/

namespace Grass.Process

universe u

/--
The acceptance data a `ProcessCorrect` proof is stated against.

Every field is supplied by the owner of the specification, never derived here.
-/
structure ProcessAcceptance (p : ProcessSpec.{u}) where
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
  /-- Which rendered views are acceptable, for a process that has a view. -/
  ViewAccepts : (facet : ViewFacet p.State) → facet.View → Prop
  /--
  Which observations the specification *demands*, as opposed to merely permits.

  This is the third disjunct of `docs/PROCESS.md` §7 progress: a cycle is
  progressing if it produces "an independently specified observation". That
  phrase is specification-relative — an observation the specification did not
  ask for cannot discharge a progress obligation, or every process could satisfy
  progress by logging — so the predicate has to come from here and not from the
  process.
  -/
  Demanded : p.Observation → Prop

namespace ProcessAcceptance

variable {p : ProcessSpec.{u}}

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
machine does what it does, not that what it does is wanted. `Demanded` is
`fun _ => False` rather than `fun _ => True`, so this acceptance cannot be used
to discharge progress by emitting anything at all.
-/
def trivial (p : ProcessSpec.{u}) : ProcessAcceptance p where
  TerminalAccepts := fun _ _ => True
  TraceAccepts := fun _ => True
  DemandsWellFormed := fun _ => True
  ViewAccepts := fun _ _ => True
  Demanded := fun _ => False

theorem trivial_demands_nothing (p : ProcessSpec.{u}) (segment : p.Segment) :
    ¬ (trivial p).SegmentIsDemanded segment := by
  rintro ⟨_, _, demanded⟩
  exact demanded

end ProcessAcceptance

end Grass.Process
