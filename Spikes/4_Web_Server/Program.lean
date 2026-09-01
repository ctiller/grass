import Grass.Emit
import Grass.Artifact.PE32Plus
import Spikes.«4_Web_Server».Assembly
import Spikes.«4_Web_Server».Cancellation

namespace Grass.Spikes.WebServer

def serverVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    using explicit_process serverProcessPlanRealizes
    using_cancellation serverCancellation
    with serverSource

def bytes : ByteArray := emitProgram serverVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  serverVerified.sound

def artifact : PE32Plus := serverVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem parserConforms (input : ByteArray) :
    PE32Plus.parse input = .error ∨
    ∃ image, PE32Plus.parse input = .ok image ∧
      PE32Plus.ConformsToSpecification input image :=
  PE32Plus.parserConforms input

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact serverVerified.rawProgram :=
  serverVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

theorem admissibleLoadsRefineHttp2 :
    ∀ load ∈ PE32Plus.admissibleLoads bytes,
      LoadedExecutionRefines load spec :=
  serverVerified.artifactCorrectness.everyAdmissibleLoad

end Grass.Spikes.WebServer
