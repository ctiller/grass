import Grass.Assembly.X86Source
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.X86Source
open Grass.Assembly SourceInput X86Source
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def spike1Program : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"
@[reducible] def parsedActual : Option (List LocatedStatement) :=
  (extractHelloSourceChars spike1Program).toOption.bind fun body => (parseBody body).toOption

/-- The unchanged Spike 1 body is consumed completely; unsupported nonblank lines
would make this result `none`. -/
-- Keep the source computation in the proposition so the kernel evaluator does
-- not stop at the separately compiled fixture abbreviation.
theorem actual_body_complete :
    ((extractHelloSourceChars spike1Program).toOption.bind fun body =>
      (parseBody body).toOption).map List.length = some 50 := by decide +kernel

def parseText (source : String) : Option (List LocatedStatement) :=
  (extractHelloSource source).toOption.bind fun body => (parseBody body).toOption

example : parseText "def helloSource := asm_source { frobnicate rax }" = none := by decide +kernel
example : parseText "def helloSource := asm_source { @audit(.orphan) }" = none := by decide +kernel
example : parseText "def helloSource := asm_source { push eax }" = none := by decide +kernel
example : parseText "def helloSource := asm_source { call qword ptr [rip + import] extra }" = none := by
  decide +kernel

example : parseText "def helloSource := asm_source { mov rax, ecx }" = none := by decide +kernel
example : parseText "def helloSource := asm_source { test r14d, rax }" = none := by decide +kernel
example : parseText "def helloSource := asm_source { @audit(foo [:=]) }" = none := by decide +kernel
example : parseText "def helloSource := asm_source { label: @audit(.broken }" = none := by decide +kernel
example : parseText "def helloSource := asm_source { label: @terminal(.success) junk }" = none := by
  decide +kernel
example : parseText "def helloSource := asm_source { label: @placement [handle r12] }" = none := by
  decide +kernel
example : parseText "def helloSource := asm_source { label: @placement [handle := r12,] }" = none := by
  decide +kernel
example : parseText "def helloSource := asm_source { label: @invariant loop(payload,) }" = none := by
  decide +kernel
example : parseText "def helloSource := asm_source { label: @placement [handle := r12, handle := r13] }" =
    none := by decide +kernel

end Grass.Tests.Assembly.X86Source
