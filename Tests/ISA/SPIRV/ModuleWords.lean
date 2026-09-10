import Grass.ISA.SPIRV.SourceParser
import Grass.ISA.SPIRV.Module

namespace Grass.Tests.ISA.SPIRV.ModuleWords
open Grass.ISA.SPIRV

/-- Generic single-block module, independent of the authored shaders. -/
def source : List Char := "OpCapability Shader
OpMemoryModel Logical GLSL450
OpEntryPoint Vertex %entry \"main\"
%void = OpTypeVoid
%fn = OpTypeFunction %void
%entry = OpFunction %void None %fn
%label = OpLabel
OpReturn
OpFunctionEnd".toList

/-- Hand-derived from the Khronos 1.5 grammar: header, capability, memory model,
entry with NUL-terminated string, types, function, label, return and end. -/
def expected : Array (BitVec 32) := #[
  0x07230203, 0x00010500, 0, 5, 0,
  0x00020011, 1,
  0x0003000e, 0, 1,
  0x0005000f, 0, 3, 0x6e69616d, 0,
  0x00020013, 1,
  0x00030021, 2, 1,
  0x00050036, 1, 3, 0, 2,
  0x000200f8, 4,
  0x000100fd,
  0x00010038]

def regression : IO Unit := do
  let actual := ((SourceParser.parseBody? source).bind (fun statements =>
    (Module.compile statements).toOption)).map Module.Output.words
  unless actual == some expected do
    throw (IO.userError "module encoding differs from independent exact-word fixture")

#eval regression

end Grass.Tests.ISA.SPIRV.ModuleWords
