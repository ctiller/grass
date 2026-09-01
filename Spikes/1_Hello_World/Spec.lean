import Grass.Spec.Console
import Spikes.«1_Hello_World».Resource

namespace Grass.Spikes.HelloWorld

def message : TextLine := "Hello, World!"

inductive HelloOutcome
  | success
  | failure

def stdoutProtocol {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : AbstractSpecificationProcessNetwork resources :=
  Console.linearStdoutProtocol resources message HelloOutcome

def helloSpec {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : Specification resources :=
  Specification.ofProcesses (stdoutProtocol resources)
    |>.withLiveness (.terminatesUnder [.environmentResponsive])

theorem helloSpecCorrect {R : Type} [ResourceModel R] [ConsoleWriteResources R]
    (resources : R) : MeetsAllSpecificationTheorems (helloSpec resources) :=
  Console.linearStdoutProtocolCorrect resources message HelloOutcome

def spec : Specification resources := helloSpec resources

end Grass.Spikes.HelloWorld
