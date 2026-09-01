import Grass.Emit
import Spikes.«5_Spinning_Cube».SourceClosure
import Spikes.«5_Spinning_Cube».Staged

namespace Grass.Spikes.SpinningCube

def shaders : ShaderSet plan :=
  { vertex := cubeVertex
    fragment := cubeFragment }

def source : MachineSource plan :=
  { host := rawCubeHost
    devices := shaders }

def cubeVerified : VerifiedProgram spec := by
  verify_assembly plan using_process stagedProcessRealization with source
    using_machine_blend cubeMachineBlendInput cubeMachineBlendInputComplete
    and_source_identity cubeSourceElaboratesExactly
    and_host_refinement rawHostImplementsDriver

def bytes : ByteArray := emitProgram cubeVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  cubeVerified.sound

end Grass.Spikes.SpinningCube
