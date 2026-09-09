import Grass.Assembly.X86ClosedEncoding
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.X86ClosedEncoding
open Grass.Assembly SourceInput X86Source X86ClosedEncoding
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def spike1Program : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"
@[reducible] def parsedActual : Option (List LocatedStatement) :=
  (extractHelloSourceChars spike1Program).toOption.bind fun body => (parseBody body).toOption

def readyCount : Option Nat := parsedActual.map fun statements =>
  (statements.filterMap fun statement => match statement.statement with
    | .instruction instruction _ => encode instruction
    | .label _ _ => none).length

example : readyCount = some 20 := by decide +kernel
example : parsedActual.bind (fun statements => statements.findSome? fun statement =>
    match statement.statement with
    | .instruction instruction _ => if encode instruction |>.isNone then some () else none
    | _ => none) = some () := by decide +kernel

example : encode ⟨.mov, [.register ⟨.rax,.w64⟩, .immediate (2^64)]⟩ = none := by decide
example : encode ⟨.mov, [.register ⟨.rax,.w32⟩, .immediate (2^32)]⟩ = none := by decide
example : encode ⟨.push, [.register ⟨.rax,.w32⟩]⟩ = none := by decide
example : encode ⟨.add, [.register ⟨.rax,.w64⟩, .register ⟨.rcx,.w32⟩]⟩ = none := by decide

end Grass.Tests.Assembly.X86ClosedEncoding
