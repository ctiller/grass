import Grass.ISA.X86.Addressing

/-!
# x86 addressing encoding examples

Small literal checks for architectural escape cases that a self-consistent
encoder/decoder round trip would not detect on its own.
-/

namespace Grass.Tests.ISA.X86.AddressingExamples

open Grass.Std.Logical Grass.ISA.X86

private def displacement : BitVec 32 := 0x11223344

/-- A RIP-relative operand uses the `rm=101` escape and no SIB byte. -/
example :
    (encodeMem (.ripRelative displacement)).map
      (fun encoding => ((encoding.modrm 2).toByte, encoding.sib)) =
      some (0x15, none) := by
  decide

/-- An `rsp` base uses the SIB escape even when no index is present. -/
example :
    (encodeMem (.base .rsp displacement)).map
      (fun encoding => ((encoding.modrm 0).toByte, encoding.sib.map (·.toByte))) =
      some (0x84, some 0x24) := by
  decide

/-- `r13` cannot use `mod=00`, whose low register bits denote RIP-relative addressing. -/
example :
    (encodeMem (.base .r13 displacement)).map (·.mod) ≠
      some ModRm.modNoDisplacement := by
  decide

/-- `rsp` is not encodable as an index register. -/
example :
    encodeMem (.baseIndex .rax .rsp .s1 displacement) = none := by
  decide

end Grass.Tests.ISA.X86.AddressingExamples
