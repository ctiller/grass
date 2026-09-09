import Grass.Console.Resources
import Grass.Console.LineBehavior

/-!
# Console-specific capture staging

This is an intermediate consumer for the existing console denotation, not an
alternate certificate root. It neither replaces `Grass.SpecProcess` nor exports
the authored specification facade. The future root migration must preserve this
exact request, resource dictionary/value, selected snapshot and appended demands.

`withLiveness_context` and `withLiveness_fragments` enforce append-only capture.
The isolated boundary timing premise deliberately has a different constructor
from the standard `environmentResponsive` assumption: coupling that standard
strategy vocabulary and terminal-status observation remains a separate proof.
-/

namespace Grass.Console

open Resource

/-- The bounded timing demand interpreted in `Grass.Console.CapturedDemands`.
It does not assert a provider or scheduler bridge. -/
inductive CapturedLiveness where
  | terminatesUnderBoundaryResponse
deriving DecidableEq

/-- Construction stores the selected snapshot alongside the authored request.
The model dictionary and resource value remain exact type indices. -/
structure CapturedContext {R : Type} [model : ResourceModel R]
    (resources : R) (Outcome : Type) where
  request : LineRequest Outcome
  resourceSemantics : ConsoleResourceSnapshot model resources

/-- The singleton console component and the ordered appended liveness fragments. -/
structure CapturedSuite {R : Type} [ResourceModel R] (resources : R) (Outcome : Type) where
  context : CapturedContext resources Outcome
  liveness : List CapturedLiveness

/-- Explicit migration staging; no certificate accepts this intermediate type. -/
structure CapturedSpecification {R : Type} [ResourceModel R]
    (resources : R) (Outcome : Type) where
  suite : CapturedSuite resources Outcome

namespace CapturedSpecification

variable {R Outcome : Type} [model : ResourceModel R] {resources : R}

/-- Capture the selected capability once, at construction of the line component. -/
def ofLine [ConsoleWriteResources R] (resources : R)
    (line : Specification.TextLine) (policy : ConsoleWriteOutcomePolicy Outcome) :
    CapturedSpecification resources Outcome :=
  ⟨⟨⟨⟨line, policy⟩, ConsoleWriteResources.captured resources⟩, []⟩⟩

def context (spec : CapturedSpecification resources Outcome) :
    CapturedContext resources Outcome := spec.suite.context

/-- Append the requested fragment to the stored suite and capture the new suite. -/
def withLiveness (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) : CapturedSpecification resources Outcome :=
  ⟨{ spec.suite with liveness := spec.suite.liveness ++ [fragment] }⟩

theorem withLiveness_context (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) : (spec.withLiveness fragment).context = spec.context := rfl

theorem withLiveness_fragments (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) :
    (spec.withLiveness fragment).suite.liveness = spec.suite.liveness ++ [fragment] := rfl

/-- Denotation is computed from the captured request; no later capability lookup
or caller-supplied replacement payload occurs in this projection. -/
def system (spec : CapturedSpecification resources Outcome)
    (rendering : Specification.LineRendering) : RelationalSystem Behavior.Event :=
  spec.context.request.system rendering

abbrev Complete (spec : CapturedSpecification resources Outcome)
    (rendering : Specification.LineRendering) := spec.context.request.Complete rendering

/-- `withLiveness_preserves_system` retains the unrestricted transition relation. -/
theorem withLiveness_preserves_system (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) (rendering : Specification.LineRendering) :
    (spec.withLiveness fragment).system rendering = spec.system rendering := rfl

/-- The unrestricted complete carrier is unchanged, including permanent waits. -/
theorem withLiveness_preserves_complete (spec : CapturedSpecification resources Outcome)
    (fragment : CapturedLiveness) (rendering : Specification.LineRendering) :
    (spec.withLiveness fragment).Complete rendering = spec.Complete rendering := rfl

end CapturedSpecification
end Grass.Console
