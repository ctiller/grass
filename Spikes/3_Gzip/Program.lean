import Grass.Emit
import Grass.Artifact.PE32Plus
import Spikes.«3_Gzip».Assembly

namespace Grass.Spikes.Gzip

def gzipVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    with gzipSource

def bytes : ByteArray := emitProgram gzipVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  gzipVerified.sound

def artifact : PE32Plus := gzipVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact gzipVerified.rawProgram :=
  gzipVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

end Grass.Spikes.Gzip
