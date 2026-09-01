import Grass.Spec.Console
import Grass.Spec.Resource

namespace Grass.Spikes.HelloWorld

def resources : ConsoleResourceModel :=
  ConsoleResourceModel.singleLine

def message : TextLine := "Hello, World!"

inductive HelloOutcome
  | success
  | failure

def helloContract {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : BehaviorContract resources :=
  Console.writeLineContract resources message HelloOutcome

def helloSpec {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.ofRelational (helloContract resources)
    |>.withLiveness (.terminatesUnder [.environmentResponsive])

theorem helloSpecCorrect {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : MeetsAllSpecificationTheorems (helloSpec resources) :=
  Console.writeLineContractCorrect resources message HelloOutcome

def spec : SpecProcess resources := helloSpec resources

end Grass.Spikes.HelloWorld
