import Grass.Artifact.PE32Plus
import Spikes.«1_Hello_World».Program

namespace Grass.Spikes.HelloWorld

def artifact : PE32Plus := helloVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact helloVerified.rawProgram :=
  helloVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

end Grass.Spikes.HelloWorld
