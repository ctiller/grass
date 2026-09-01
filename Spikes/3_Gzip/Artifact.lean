import Grass.Artifact.PE32Plus
import Spikes.«3_Gzip».Program

namespace Grass.Spikes.Gzip

def artifact : PE32Plus := gzipVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact gzipVerified.rawProgram :=
  gzipVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

end Grass.Spikes.Gzip
