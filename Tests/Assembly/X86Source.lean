import Grass.Assembly.X86Source
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.X86Source
open Grass.Assembly SourceInput X86Source
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def parseText (source : String) : Option (List LocatedStatement) :=
  (extractSource source).toOption.bind fun body => (parseBody body).toOption

example : parseText "def parseSample := asm_source { frobnicate rax }" = none := by decide +kernel
example : parseText "def parseSample := asm_source { @audit(.orphan) }" = none := by decide +kernel
example : parseText "def parseSample := asm_source { push eax }" = none := by decide +kernel
example : parseText "def parseSample := asm_source { call qword ptr [rip + import] extra }" = none := by
  decide +kernel

example : parseText "def parseSample := asm_source { mov rax, ecx }" = none := by decide +kernel
example : parseText "def parseSample := asm_source { test r14d, rax }" = none := by decide +kernel
example : parseText "def parseSample := asm_source { @audit(foo [:=]) }" = none := by decide +kernel
example : parseText "def parseSample := asm_source { label: @audit(.broken }" = none := by decide +kernel
example : parseText "def parseSample := asm_source { label: @terminal(.success) junk }" = none := by
  decide +kernel
example : parseText "def parseSample := asm_source { label: @placement [handle r12] }" = none := by
  decide +kernel
example : parseText "def parseSample := asm_source { label: @placement [handle := r12,] }" = none := by
  decide +kernel
example : parseText "def parseSample := asm_source { label: @invariant loop(payload,) }" = none := by
  decide +kernel
example : parseText "def parseSample := asm_source { label: @placement [handle := r12, handle := r13] }" =
    none := by decide +kernel

end Grass.Tests.Assembly.X86Source
