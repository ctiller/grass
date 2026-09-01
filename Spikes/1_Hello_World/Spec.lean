import Grass.Spec.Console
import Grass.Spec.Resource

namespace Grass.Spikes.HelloWorld

def resources : ConsoleResourceModel :=
  ConsoleResourceModel.singleLine

def message : TextLine := "Hello, World!"

inductive HelloOutcome
  | success
  | failure

def outcomePolicy : ConsoleWriteOutcomePolicy HelloOutcome where
  success := .success
  stdoutUnavailable := .failure
  writeFailed := .failure
  noProgress := .failure

def helloContract {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : BehaviorContract resources :=
  Console.writeLineContract resources message outcomePolicy

def helloSpec {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.ofRelational (helloContract resources)
    |>.withLiveness (.terminatesUnder [.environmentResponsive])

theorem helloSpecCorrect {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : MeetsAllSpecificationTheorems (helloSpec resources) :=
  Console.writeLineContractCorrect resources message outcomePolicy

def spec : SpecProcess resources := helloSpec resources

end Grass.Spikes.HelloWorld
