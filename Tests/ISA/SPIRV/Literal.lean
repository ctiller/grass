import Grass.ISA.SPIRV.Literal
import Grass.Trust.Audit

namespace Grass.Tests.ISA.SPIRV.Literal
open Grass.ISA.SPIRV.Literal

example : parseWord32? "4294967295" = some 0xffffffff := by decide
example : parseWord32? "4294967296" = none := by decide
example : int32? true "-2147483648" = some 0x80000000 := by decide
example : int32? true "2147483648" = none := by decide
example : int32? false "-1" = none := by decide
example : float32Exact? "1.0" = some 0x3f800000 := by decide
example : float32Exact? "-1.0" = some 0xbf800000 := by decide
example : float32Exact? "0.25" = some 0x3e800000 := by decide
example : float32Exact? "3.0" = some 0x40400000 := by decide
example : float32Exact? "-0.0" = some 0x80000000 := by decide
example : float32Exact? "16777217.0" = none := by decide
example : float32Exact? "0.1" = none := by decide
example : float32Exact? "NaN" = none := by decide
example : float32Exact? "1.0.0" = none := by decide
example : float32Exact? "1e0" = none := by decide
example : float32Exact? ".25" = none := by decide

#print axioms float32Exact?_sound
#audit_runtime_dependencies Grass.ISA.SPIRV.Literal.float32Exact?

end Grass.Tests.ISA.SPIRV.Literal
