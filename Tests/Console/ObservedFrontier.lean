import Grass.Console.ObservedFrontier
import Grass.Console.Contract
import Grass.Semantics.SpecProcess

/-! The exact generic contract binding used by Hello's authored specification. -/

namespace Grass.Tests.Console.ObservedFrontier

open Grass
open Grass.Console
open Grass.RelationalSystem
variable {R Outcome : Type} [Resource.ResourceModel R] [ConsoleWriteResources R]

def request (line : Specification.TextLine) (policy : ConsoleWriteOutcomePolicy Outcome) :
    LineRequest Outcome := ⟨line, policy⟩

/-- The write-line contract used by Hello denotes exactly the observed model. -/
theorem writeLine_denotation_exact (resources : R) (line : Specification.TextLine)
    (policy : ConsoleWriteOutcomePolicy Outcome) (rendering : Specification.LineRendering) :
    (Console.writeLineContract resources line policy).denotation rendering () =
      ObservedBehavior.model (request line policy) rendering := rfl

/-- Thus every actual history of a captured write-line denotation is terminal or
can permanently wait on its exact pending output/observation occurrence. -/
theorem writeLine_terminal_or_permitted_wait (resources : R) (line : Specification.TextLine)
    (policy : ConsoleWriteOutcomePolicy Outcome) (rendering : Specification.LineRendering)
    (history : ((Console.writeLineContract resources line policy).denotation rendering ()).system.History) :
    ((Console.writeLineContract resources line policy).denotation rendering ()).system.Terminal
        history.state history.graph ∨
      Nonempty (PermanentWait
        ((Console.writeLineContract resources line policy).denotation rendering ()).boundary history) := by
  exact ObservedBehavior.terminal_or_permitted_wait (request line policy) rendering history

/-- The same statement at the `SpecProcess` constructor used by `helloSpec`.
Adding a liveness request changes no denotation and supplies no assumption to
this proof. -/
theorem writeLine_withLiveness_terminal_or_permitted_wait
    (resources : R) (line : Specification.TextLine)
    (policy : ConsoleWriteOutcomePolicy Outcome) (rendering : Specification.LineRendering)
    (liveness : LivenessContract)
    (history : (((SpecProcess.ofRelational
        (Console.writeLineContract resources line policy)).withLiveness liveness).denotation
        rendering ()).system.History) :
    (((SpecProcess.ofRelational
        (Console.writeLineContract resources line policy)).withLiveness liveness).denotation
        rendering ()).system.Terminal history.state history.graph ∨
      Nonempty (PermanentWait
        (((SpecProcess.ofRelational
          (Console.writeLineContract resources line policy)).withLiveness liveness).denotation
          rendering ()).boundary history) :=
  ObservedBehavior.terminal_or_permitted_wait (request line policy) rendering history

end Grass.Tests.Console.ObservedFrontier
