import Grass.Emit
import Spikes.«5_Spinning_Cube».Assembly
import Spikes.«5_Spinning_Cube».Process

namespace Grass.Spikes.SpinningCube

def shaders : ShaderSet plan :=
  { vertex := cubeVertex
    fragment := cubeFragment }

def source : MachineSource plan :=
  { host := cubeHost
    devices := shaders }

def sourceConnections : HeterogeneousSourceConnections plan source :=
  machine_connections {
    callback `wndproc =>
      Win32.windowStatePointer
        (installAt := .wmNcCreate)
        (clearAt := .wmNcDestroy)
    shader `vertexShader =>
      Spirv.module cubeVertex
        (entry := `main)
        (staticRange := `cubeVertexBytes)
        (createCall := `vkCreateShaderModule)
        (codeSize := `cubeVertexBytes.size)
        (codePointer := `cubeVertexBytes.address)
        (returnedHandle := `vertModule)
        (pipelineStage := (`shaderStages, 0, VERTEX_BIT))
        (entryName := `mainName)
    shader `fragmentShader =>
      Spirv.module cubeFragment
        (entry := `main)
        (staticRange := `cubeFragmentBytes)
        (createCall := `vkCreateShaderModule)
        (codeSize := `cubeFragmentBytes.size)
        (codePointer := `cubeFragmentBytes.address)
        (returnedHandle := `fragModule)
        (pipelineStage := (`shaderStages, 1, FRAGMENT_BIT))
        (entryName := `mainName)
    pushConstant `rotation => rotationRepresentation
  }

theorem sourceConnectionsCorrect :
    HeterogeneousSourceConnections.Valid sourceConnections := by
  verify_machine_connections
    using_rotation rotationRepresentationCorrect

def cubeVerified : VerifiedProgram spec := by
  verify_assembly plan
    using_process stagedProcessRealization
    using_models vertexModelCorrect fragmentModelCorrect
    using_machine_proofs hostImplementsDriver vertexCorrect fragmentCorrect
    using_connections sourceConnectionsCorrect
    with source

def bytes : ByteArray := emitProgram cubeVerified

end Grass.Spikes.SpinningCube
