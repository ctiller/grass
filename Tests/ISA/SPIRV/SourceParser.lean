import Grass.ISA.SPIRV.SourceParser

namespace Grass.Tests.ISA.SPIRV.SourceParser

open Grass.ISA.SPIRV.SourceParser
open Grass.ISA.SPIRV.SourceSyntax

def multipleInstructions : List Char := "%i=OpC %t 0  %j=OpC %t 1".toList
def multilineEntryPoint : List Char := "OpE %m \"main\"\n %o".toList

private def requireEqual {α : Type} [DecidableEq α]
    (label : String) (actual expected : α) : IO Unit :=
  if actual = expected then pure () else throw (IO.userError label)

#eval do
  requireEqual "same-line statements retain exact source spans"
    (parseBody? multipleInstructions)
    (some [
      ⟨some "i", "OpC", [.id "t", .word "0"], 0, 11⟩,
      ⟨some "j", "OpC", [.id "t", .word "1"], 13, 24⟩])
  requireEqual "quoted operands and newlines remain in one statement"
    (parseBody? multilineEntryPoint)
    (some [⟨none, "OpE", [.id "m", .quoted "main", .id "o"], 0, 17⟩])
  requireEqual "an orphan quoted token is rejected"
    (parseBody? "\"orphan\" OpReturn".toList) none
  requireEqual "a result assignment needs an opcode"
    (parseBody? "%x = word".toList) none
  requireEqual "comments are explicitly unsupported"
    (parseBody? "OpReturn; ignored".toList) none
  requireEqual "backslash escapes are explicitly unsupported"
    (parseBody? "OpName %x \"a\\\"b\"".toList) none
  requireEqual "unterminated strings are rejected"
    (parseBody? "OpName %x \"unterminated".toList) none

example {body : List Char} {statements : List Statement}
    (parsed : parseBody? body = some statements) :
    ∀ statement ∈ statements, Statement.Framed body statement = true :=
  parseBody?_framed parsed

end Grass.Tests.ISA.SPIRV.SourceParser
