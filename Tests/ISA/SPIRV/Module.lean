import Grass.ISA.SPIRV.Module

namespace Tests.ISA.SPIRV.Module
open Grass.ISA.SPIRV SourceSyntax

private def s (result : Option String) (opcode : String) (operands : List Atom) : Statement :=
  { result, opcode, operands, start := 0, finish := 0 }

private def duplicate : List Statement :=
  [s (some "x") "OpTypeVoid" [], s (some "x") "OpTypeBool" []]

example : Grass.ISA.SPIRV.Module.compile duplicate = .error "duplicate result ID %x" := by rfl

private def unsupported : List Statement :=
  [s none "OpCapability" [.word "Shader"], s none "OpMemoryModel" [.word "Logical", .word "GLSL450"],
   s none "OpKill" []]

example : (Grass.ISA.SPIRV.Module.compile unsupported).isOk = false := by decide

private def mistypedLoad : List Statement :=
  [s none "OpCapability" [.word "Shader"], s none "OpMemoryModel" [.word "Logical", .word "GLSL450"],
   s (some "void") "OpTypeVoid" [], s (some "fn") "OpTypeFunction" [.id "void"],
   s (some "main") "OpFunction" [.id "void", .word "None", .id "fn"],
   s (some "label") "OpLabel" [], s (some "bad") "OpLoad" [.id "void", .id "main"],
   s none "OpReturn" [], s none "OpFunctionEnd" []]

example : (Grass.ISA.SPIRV.Module.compile mistypedLoad).isOk = false := by decide

private def beforeLabel : List Statement :=
  [s none "OpCapability" [.word "Shader"],
   s none "OpMemoryModel" [.word "Logical", .word "GLSL450"],
   s (some "void") "OpTypeVoid" [],
   s (some "fn") "OpTypeFunction" [.id "void"],
   s (some "main") "OpFunction" [.id "void", .word "None", .id "fn"],
   s (some "bad") "OpLoad" [.id "void", .id "main"]]

private def afterReturn : List Statement :=
  [s none "OpCapability" [.word "Shader"],
   s none "OpMemoryModel" [.word "Logical", .word "GLSL450"],
   s (some "void") "OpTypeVoid" [],
   s (some "fn") "OpTypeFunction" [.id "void"],
   s (some "main") "OpFunction" [.id "void", .word "None", .id "fn"],
   s (some "label") "OpLabel" [], s none "OpReturn" [],
   s none "OpStore" [.id "main", .id "main"]]

private def badBlockTarget : List Statement :=
  [s none "OpCapability" [.word "Shader"],
   s none "OpMemoryModel" [.word "Logical", .word "GLSL450"],
   s none "OpEntryPoint" [.word "Vertex", .id "main", .quoted "entry"],
   s none "OpDecorate" [.id "void", .word "Block"],
   s (some "void") "OpTypeVoid" [],
   s (some "fn") "OpTypeFunction" [.id "void"],
   s (some "main") "OpFunction" [.id "void", .word "None", .id "fn"],
   s (some "label") "OpLabel" [], s none "OpReturn" [], s none "OpFunctionEnd" []]

private def badMemberIndex : List Statement :=
  [s none "OpCapability" [.word "Shader"],
   s none "OpMemoryModel" [.word "Logical", .word "GLSL450"],
   s none "OpEntryPoint" [.word "Vertex", .id "main", .quoted "entry"],
   s none "OpMemberDecorate" [.id "record", .word "1", .word "Offset", .word "0"],
   s (some "void") "OpTypeVoid" [],
   s (some "record") "OpTypeStruct" [.id "void"],
   s (some "fn") "OpTypeFunction" [.id "void"],
   s (some "main") "OpFunction" [.id "void", .word "None", .id "fn"],
   s (some "label") "OpLabel" [], s none "OpReturn" [], s none "OpFunctionEnd" []]

private def requireRejected (expected : String) (source : List Statement) : IO Unit :=
  match Grass.ISA.SPIRV.Module.compile source with
  | .error actual => if actual == expected then pure ()
      else throw (IO.userError s!"expected {expected}, got {actual}")
  | .ok _ => throw (IO.userError s!"expected specific rejection: {expected}")

#eval do
  requireRejected "misplaced OpLoad" beforeLabel
  requireRejected "misplaced OpStore" afterReturn
  requireRejected "Block decoration target is not a structure type" badBlockTarget
  requireRejected "member Offset index is out of bounds" badMemberIndex

end Tests.ISA.SPIRV.Module
