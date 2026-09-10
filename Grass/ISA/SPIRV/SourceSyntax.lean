/-! Lossless operand categories for a bounded SPIR-V assembly source reader.
Character offsets refer to the captured module body, not a reprinted copy.
These are syntax values; constructors alone certify no typing or encoding.
-/
namespace Grass.ISA.SPIRV.SourceSyntax

inductive Atom where
  | id (name : String)
  | word (text : String)
  | quoted (text : String)
  deriving DecidableEq, Repr

structure Statement where
  result : Option String
  opcode : String
  operands : List Atom
  start : Nat
  finish : Nat
  deriving DecidableEq, Repr

end Grass.ISA.SPIRV.SourceSyntax
