import Grass.Assembly.SignedRel32

namespace Grass.Tests.Assembly.SignedRel32

open Grass.Assembly.SignedRel32

example : (resolve? 100 5 120).map Resolved.bits =
    some (BitVec.ofInt 32 15) := by decide

example : (resolve? 100 5 90).map Resolved.bits =
    some (BitVec.ofInt 32 (-15)) := by decide

/-- Both signed endpoints are tested: the lower endpoint is inclusive. -/
example : (resolve? 0 (2 ^ 31) 0).isSome := by decide
example : resolve? 0 (2 ^ 31 + 1) 0 = none := by decide

/-- The upper endpoint is exclusive. -/
example : (resolve? 0 0 (2 ^ 31 - 1)).isSome := by decide
example : resolve? 0 0 (2 ^ 31) = none := by decide

/-- Resolution uses the next instruction, rather than its starting address. -/
example : (resolve? 100 5 120).map Resolved.bits ≠
    (resolve? 100 0 120).map Resolved.bits := by decide

example {resolved : Resolved} (h : resolve? 100 5 120 = some resolved) :
    (120 : Int) = (100 : Int) + (5 : Int) + resolved.bits.toInt :=
  target_equation_of_resolve? h

end Grass.Tests.Assembly.SignedRel32
