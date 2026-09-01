import Grass.Platform.Win10.X64
import Spikes.«1_Hello_World».Spec

namespace Grass.Spikes.HelloWorld

def policy : TargetOutcomeProjection HelloOutcome UInt32 :=
  .successOrFailure
    (success := HelloOutcome.success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ConsoleText
    (newline := .crlf)
    (encoding := .utf8)
    (outcome := policy)

end Grass.Spikes.HelloWorld
