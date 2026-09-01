import Grass.Process.Sequential
import Spikes.«1_Hello_World».Spec

namespace Grass.Spikes.HelloWorld

def stdoutProtocol : AbstractSpecificationProcessNetwork resources :=
  Console.linearStdoutProtocol resources message HelloOutcome

def stdoutPresentation : ProcessPresentation spec where
  network := stdoutProtocol
  denotationExact := Console.linearStdoutProtocolDenotesWriteLineContract
  requirementsExact := Console.linearStdoutProtocolRequirementsExact

def processRealization : ProcessRealization spec :=
  ProcessRealization.standard
    (Grass.Std.Realizers.lookupExact stdoutPresentation)

end Grass.Spikes.HelloWorld
