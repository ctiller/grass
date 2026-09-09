import Grass.ISA.X86.Execution.DecodedSite
import Grass.ISA.X86.BasicInstructions

namespace Grass.Tests.ISA.X86.ExecutionDecodedSite
open Grass.ISA.X86 Grass.ISA.X86.Execution Grass.Std.Logical

private def accepted {α β : Type} : Except α β → Bool
  | .ok _ => true
  | .error _ => false

example : accepted (DecodedSite.check 0x1000 [0x41, 0x54, 0x90]) = true := by decide
example : accepted (DecodedSite.check 0x1000 [0x48, 0x83, 0xEC, 48]) = true := by decide
-- The whole observed stream is needed; an incomplete REX does not certify a site.
example : accepted (DecodedSite.check 0x1000 [0x41]) = false := by decide
-- The next PC may not wrap even if decoding the bytes would succeed.
example : accepted (DecodedSite.check (BitVec.ofNat 64 (2^64-1)) [0x90]) = false := by decide
example : accepted (DecodedSite.check 0x1000 [0x48, 0x66, 0x89, 0xC0]) = false := by decide

end Grass.Tests.ISA.X86.ExecutionDecodedSite
