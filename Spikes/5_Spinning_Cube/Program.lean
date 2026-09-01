import Grass.Emit
import Grass.Artifact.PE32Plus
import Spikes.«5_Spinning_Cube».Assembly
import Spikes.«5_Spinning_Cube».Layout
import Spikes.«5_Spinning_Cube».Process

namespace Grass.Spikes.SpinningCube

def shaders : ShaderSet plan :=
  { vertex := cubeVertex
    fragment := cubeFragment }

def source : MachineSource plan :=
  { host := cubeHost
    devices := shaders }

def cubeVerified : VerifiedProgram spec := by
  verify_assembly plan
    using_process stagedProcessRealization
    using_models vertexModelCorrect fragmentModelCorrect
    with source

def bytes : ByteArray := emitProgram cubeVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  cubeVerified.sound

def vertexWords : Vec UInt32 := Spirv.writeWords cubeVertex

def fragmentWords : Vec UInt32 := Spirv.writeWords cubeFragment

theorem vertexRoundTrip :
    Spirv.parseWords vertexWords = .ok cubeVertex :=
  Spirv.writeWords_parse cubeVertex

theorem fragmentRoundTrip :
    Spirv.parseWords fragmentWords = .ok cubeFragment :=
  Spirv.writeWords_parse cubeFragment

def artifact : PE32Plus := cubeVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem hostTextDecodesExactly :
    LoadedHostTextDecodesTo artifact cubeVerified.rawProgram.host :=
  cubeVerified.artifactCorrectness.loadedHostTextDecodes

theorem embeddedVertexExactly :
    EmbeddedWordsAt artifact cubeVerified.layout.vertexRva vertexWords :=
  cubeVerified.artifactCorrectness.embeddedVertex

theorem embeddedFragmentExactly :
    EmbeddedWordsAt artifact cubeVerified.layout.fragmentRva fragmentWords :=
  cubeVerified.artifactCorrectness.embeddedFragment

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

end Grass.Spikes.SpinningCube
