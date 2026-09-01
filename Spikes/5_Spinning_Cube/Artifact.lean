import Grass.Artifact.PE32Plus
import Spikes.«5_Spinning_Cube».Program

namespace Grass.Spikes.SpinningCube

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

theorem processPlanExact : cubeVerified.process.plan = processPlan := rfl

theorem machineSourceExact : cubeVerified.machineSource = source := rfl

structure CrossIsaArtifactConnection
    (artifact : Artifact cubeVerified.realization) where
  process : ProcessPlanRealizes spec cubeVerified.process.plan
  driver : ProcessDriver spec cubeVerified.process.plan
    cubeVerified.process.correct cubeVerified.realization cubeVerified.ghostProgram
  assembly : AssemblyImplements
    cubeVerified.platformContract cubeVerified.machineSource
  exactArtifact : artifact = cubeVerified.linkedArtifact
  host : PETextRepresents cubeVerified.rawProgram.host artifact
  vertexRange : ExactReadOnlyRange artifact vertexWords
  fragmentRange : ExactReadOnlyRange artifact fragmentWords
  vertexCall : EveryShaderCreateUse host.trace .vertex = vertexRange
  fragmentCall : EveryShaderCreateUse host.trace .fragment = fragmentRange
  vertexModule : PipelineStageUsesCreatedModule
    host.trace .vertex .main vertexCall
  fragmentModule : PipelineStageUsesCreatedModule
    host.trace .fragment .main fragmentCall
  provider : VulkanConsumesSpirvSemantics
    plan vertexWords fragmentWords vertexCorrect fragmentCorrect

theorem artifactConnection :
    CrossIsaArtifactConnection cubeVerified.linkedArtifact :=
  cubeVerified.artifactCorrectness.crossIsaConnection

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

end Grass.Spikes.SpinningCube
