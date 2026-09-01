import Grass.Artifact.PE32Plus
import Spikes.«2_Sort».Program

namespace Grass.Spikes.Sort

def artifact : PE32Plus := sortVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact sortVerified.rawProgram :=
  sortVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

end Grass.Spikes.Sort
