import Grass.Assembly.FrameAllocation

namespace Grass.Tests.Assembly.FrameAllocation
open Grass.Assembly.FrameAllocation Grass.ABI.Win64

def frame (localBytes : Nat) : CallFrameLayout :=
  { argumentCount := 5, localBytes, localAlignment := 4,
    savedRegisters := [.r12, .r13, .r14] }

example : (resolve? (frame 4)).map (fun resolved => resolved.encoding.toBytes) =
    some [0x48, 0x83, 0xEC, 0x30] := by decide
example : (resolve? (frame 4)).map (fun resolved => resolved.immediate.toInt) =
    some 48 := by decide

-- An allocation of 128 needs the wider instruction operand, even though it
-- still fits the unwind format's separate small-allocation representation.
example : (resolve? (frame 88)).map (fun resolved => resolved.encoding.toBytes) =
    some [0x48, 0x81, 0xEC, 0x80, 0, 0, 0] := by decide

-- With three saved registers the computed call allocation is a multiple of
-- sixteen. These fixtures hit its last representable value and the first
-- rejected signed-i32 value exactly, rather than relying on a larger local.
def largestSignedFrame : CallFrameLayout := frame (2 ^ 31 - 56)
def signedUpperFrame : CallFrameLayout := frame (2 ^ 31 - 40)

example : largestSignedFrame.callAllocationBytes = 2 ^ 31 - 16 := by decide
example : (resolve? largestSignedFrame).isSome := by decide
example : signedUpperFrame.callAllocationBytes = 2 ^ 31 := by decide
example : resolve? signedUpperFrame = none := by decide

end Grass.Tests.Assembly.FrameAllocation
