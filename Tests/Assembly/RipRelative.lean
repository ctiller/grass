import Grass.Assembly.RipRelative

namespace Grass.Tests.Assembly.RipRelative
open Grass.Assembly.RipRelative Grass.ISA.X86

def view (result : Result) : Nat × Nat × List (BitVec 8) :=
  (result.sourceOffset, result.targetOffset, result.encoding.toBytes)

-- The call addresses the import slot, rather than encoding a direct branch.
example : (resolve? .indirectCall 16 0).map view =
    some (16, 0, [0xff, 0x15, 0xea, 0xff, 0xff, 0xff]) := by decide +kernel
example : (resolve? (.address .r13) 0 16).map view =
    some (0, 16, [0x4c, 0x8d, 0x2d, 9, 0, 0, 0]) := by decide +kernel

-- A common image-base shift leaves the emitted displacement unchanged.
example : (resolve? (.address .r13) 0 16).map (·.encoding.toBytes) =
    (resolve? (.address .r13) 4096 4112).map (·.encoding.toBytes) := by decide +kernel

-- Boundary probes derive next-IP from the actual encoder's size.
def boundary? (kind : Kind) (sourceOffset : Nat) (delta : Nat) : Option Result := do
  let template ← encode? kind 0
  resolve? kind sourceOffset (sourceOffset + template.size + delta)

example : (boundary? .indirectCall 0 (2 ^ 31 - 1)).isSome = true := by decide +kernel
example : (boundary? .indirectCall 0 (2 ^ 31)).isNone = true := by decide +kernel
example : (boundary? (.address .rax) 0 (2 ^ 31 - 1)).isSome = true := by decide +kernel
example : (boundary? (.address .rax) 0 (2 ^ 31)).isNone = true := by decide +kernel

def backwards? (delta : Nat) : Option Result := do
  let template ← encode? .indirectCall 0
  resolve? .indirectCall (delta - template.size) 0

example : (backwards? (2 ^ 31)).isSome = true := by decide +kernel
example : (backwards? (2 ^ 31 + 1)).isNone = true := by decide +kernel

end Grass.Tests.Assembly.RipRelative
