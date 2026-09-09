import Grass.Semantics.SpecProcess
import Grass.Console.Resources
import Grass.Console.ObservedBehavior
import Grass.Console.Accounting

namespace Grass.Console
open Resource Specification RelationalSystem

/-- The outcome type belongs to the captured authored line. -/
structure LineSyntax where
  Outcome : Type
  request : LineRequest Outcome

def lineDemands {R Outcome : Type} [model : ResourceModel R] {resources : R}
    (request : LineRequest Outcome) (snapshot : ConsoleResourceSnapshot model resources) :
    List AuthoredDemand :=
  [⟨.functional,
      ∀ rendering (history : (ObservedBehavior.system request rendering).History),
        ObservedBehavior.emittedBytes history.path.events = ObservedBehavior.committed history.state,
      [⟨"Grass.Console", "logicalText"⟩, ⟨"Grass.Console", "responseLaw"⟩]⟩,
   ⟨.progress,
      ∀ rendering,
        (∀ cut, Nonempty (PermanentWait (ObservedBehavior.boundary request rendering)
          (ObservedBehavior.writingAt request rendering cut))) ∧
        (∀ selection : ObservedBehavior.Selection request rendering,
        Nonempty (PermanentWait (ObservedBehavior.boundary request rendering)
          (ObservedBehavior.reportingAt request rendering selection))),
      [⟨"Grass.Console", "responseLaw"⟩, ⟨"Grass.Console", "terminalObservation"⟩]⟩,
   ⟨.resource, snapshot.selectedAxes = [], [⟨"Grass.Console", "resourceSelection"⟩]⟩]

/-- Console denotation uses writing, reporting, and observed phases. -/
def lineLanguage (R : Type) (model : ResourceModel R) : BehaviorLanguage R model where
  Syntax := LineSyntax
  Snapshot := ConsoleResourceSnapshot model
  Input := fun _ => Unit
  Outcome := fun authored => authored.Outcome
  Interpretation := fun _ => LineRendering
  admits := fun _ _ => True
  denotation := fun _ authored _ rendering _ => ObservedBehavior.model authored.request rendering
  demands := fun _ authored snapshot => lineDemands authored.request snapshot

/-- Build the console contract from an already selected resource snapshot. -/
def ofCapturedLine {R Outcome : Type} [model : ResourceModel R] {resources : R}
    (request : LineRequest Outcome) (snapshot : ConsoleResourceSnapshot model resources) :
    BehaviorContract resources :=
  ⟨lineLanguage R model, ⟨Outcome, request⟩, snapshot⟩

/-- Capture the console resource capability at the authored construction site. -/
def writeLineContract {R Outcome : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) (line : TextLine) (policy : ConsoleWriteOutcomePolicy Outcome) :
    BehaviorContract resources :=
  ofCapturedLine ⟨line, policy⟩ (ConsoleWriteResources.captured resources)

/-- A console view carries correspondence to the exact root, including every
interpretation and input. Projections retain this value after construction. -/
class ContractView {R : Type} [model : ResourceModel R] {resources : R}
    (contract : BehaviorContract resources) where
  request : LineRequest contract.Outcome
  snapshot : ConsoleResourceSnapshot model resources
  captured : contract = ofCapturedLine request snapshot
  interpret : LineRendering → contract.Interpretation
  rendering : contract.Interpretation → LineRendering
  interpret_rendering : ∀ value, interpret (rendering value) = value
  rendering_interpret : ∀ value, rendering (interpret value) = value
  input : contract.Input
  input_unique : ∀ value, value = input
  model_exact : ∀ interpretation value,
    contract.denotation interpretation value = ObservedBehavior.model request (rendering interpretation)

instance capturedLineView {R Outcome : Type} [model : ResourceModel R] {resources : R}
    (request : LineRequest Outcome) (snapshot : ConsoleResourceSnapshot model resources) :
    ContractView (ofCapturedLine request snapshot) where
  request := request
  snapshot := snapshot
  captured := rfl
  interpret := id
  rendering := id
  interpret_rendering := fun _ => rfl
  rendering_interpret := fun _ => rfl
  input := ()
  input_unique := fun value => by cases value; rfl
  model_exact := fun _ _ => rfl

instance writeLineView {R Outcome : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) (line : TextLine) (policy : ConsoleWriteOutcomePolicy Outcome) :
    ContractView (writeLineContract resources line policy) :=
  capturedLineView ⟨line, policy⟩ (ConsoleWriteResources.captured resources)

end Grass.Console
