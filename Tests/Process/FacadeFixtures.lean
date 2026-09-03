import Grass.Process

/-!
# The authoring facade is sufficient, and it is bounded

`Grass/Process.lean` claims two things a module cannot check about itself: that a
process author can work against `import Grass.Process` alone, and that the
facade does not drag the whole layer in behind it.

This file imports **only** that facade. Everything below therefore elaborates
against exactly the vocabulary a spike author would have, and the `#guard_msgs`
block at the end is the bound: seven modules' worth of machinery does not
resolve, so widening `Grass/Process.lean`'s four-line import list breaks this
file rather than passing unnoticed.

That is the same lesson `g-foundation:46` taught about
`Tests/Process/LayeringSpecificationOnly.lean`, applied before it could be
taught again: an import list is only a check if something fails when it changes.

`Tests/Process/FacadeCancellationFixtures.lean` does the other facet, whose
bound runs the other way — a cancellation author sees no network at all.
-/

namespace Grass.Process.Tests.Facade

open Grass.Process
open Grass.Specification

/-! ## A process, authored against the facade alone -/

/-- What the outside world can tell this process. -/
inductive Tick
  | tick
  deriving DecidableEq, Repr

/-- What it can ask for. -/
inductive Ask
  | wait
  deriving DecidableEq, Repr

/-- What it hears back. -/
@[reducible] def Answer : Ask → Type
  | .wait => Unit

/-- What it may say. -/
inductive Note
  | done
  deriving DecidableEq, Repr

/-- Why an outstanding ask was abandoned. -/
inductive Given
  | givenUp
  deriving DecidableEq, Repr

/--
The vocabulary.

`ProcessVocabulary` is reachable through the facade, which it has to be: an
author writes one before anything else.
-/
@[reducible] def vocabulary : ProcessVocabulary.{0} where
  ExternalEvent := Tick
  Demand := Ask
  Result := Answer
  Observation := Note
  InterruptReason := Given
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

/--
A process that counts down and stops.

The point is not the process — it is that this declaration typechecks with
`import Grass.Process` and nothing else. `ProcessSpec`, `ProcessVocabulary` and
the shape of `Initial`, `Terminal` and `Step` all arrive through the facade.
-/
@[reducible] def countdown : ProcessSpec.{0, 0} where
  vocabulary := vocabulary
  Request := Nat
  State := Nat
  TerminalResult := Unit
  Initial := fun request state issued emitted =>
    state = request ∧ issued = 0 ∧ emitted = []
  Terminal := fun _ state _ => state = 0
  Step := fun state event after issued emitted =>
    event = .external .tick ∧ 0 < state ∧ after = state - 1 ∧
      issued = 0 ∧ emitted = []
  view := none

/-- A boundary the facade also reaches, down the `coord1:5` diamond. -/
@[reducible] def boundary : DriverBoundary.{0} where
  ExternalEvent := Tick
  Demand := Ask
  Result := Answer
  Observation := Note
  requirements := RequirementSet.empty

/--
And an author can name the correctness record they owe.

Not discharged here — that is what `Tests/Process/M1CorrectFixtures.lean` is for,
and it needs machinery this facade deliberately does not carry. What matters is
that the *obligation* is nameable from the authoring surface, since an author
who cannot say what they owe cannot discharge it either.
-/
example (accept : ProcessAcceptance countdown) : Type 1 :=
  ProcessCorrect countdown accept

/--
As is the acceptance predicate it is indexed by, which is the specification's
side of the same obligation.
-/
example : Type 1 := ProcessAcceptance countdown

/-- And the registry and plan types, for the authors who need a network. -/
example : Type 1 := ProtocolRegistry.{0, 0, 0}

/-! ## And the facade is bounded

Each name below belongs to a module `Grass/Process.lean` deliberately does not
import. If its import list grows to reach one of them, the corresponding guard
stops matching and this file fails — which is what makes "bounded" a property of
the build rather than of the docstring.

`docs/DECISIONS.md` decision 134 draws the line between a bounded facade and a
forbidden aggregate, and these are where that line currently sits.
-/

/-! Mailboxes and selective receive: a realization's, not an author's. -/

/--
error: Unknown identifier `Grass.Process.Mailbox`
-/
#guard_msgs in
example := Grass.Process.Mailbox

/-! The structural network. -/

/--
error: Unknown identifier `Grass.Process.StructuralProcessNetwork`
-/
#guard_msgs in
example := Grass.Process.StructuralProcessNetwork

/-! Child bindings. -/

/--
error: Unknown identifier `Grass.Process.ChildDemandBinding`
-/
#guard_msgs in
example := Grass.Process.ChildDemandBinding

/-! Cross-vocabulary delivery. -/

/--
error: Unknown identifier `Grass.Process.VocabularyDelivery`
-/
#guard_msgs in
example := Grass.Process.VocabularyDelivery

/-! The transition family. -/

/--
error: Unknown identifier `Grass.Process.NetworkTransition`
-/
#guard_msgs in
example := Grass.Process.NetworkTransition

/-! Commit coalescing. -/

/--
error: Unknown identifier `Grass.Process.Coalescing`
-/
#guard_msgs in
example := Grass.Process.Coalescing

/-!
And cancellation, which decision 134 makes a separate facet. This is the guard
that would catch the most tempting mistake: folding cancellation into the main
facade because one spike happens to need both.
-/

/--
error: Unknown identifier `Grass.Process.CancellationPolicy`
-/
#guard_msgs in
example := Grass.Process.CancellationPolicy

end Grass.Process.Tests.Facade
