import Grass.ISA.X86.Execution.StoreCandidate

namespace Grass.Tests.ISA.X86.StoreCandidate

open Grass.Core Grass.Memory Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution Grass.ISA.X86.Execution.StoreCandidate

private def machine : MachineState := MachineState.initial .empty

private def stateAt (rip rcx : BitVec 64) : State :=
  { machine := machine
    gpr := fun register => if register = .rcx then rcx else 0
    rip := rip
    rflags := 0 }

private def checkError (bytes : ByteSeq) : Option Error :=
  match check 0x1000 bytes (stateAt 0x1000 0x2000) with
  | .error error => some error
  | .ok _ => none

-- `C7 01 id` is the controlled corpus initialization store `[rcx] = 11`.
example : (check 0x1000 [0xC7, 0x01, 0x0B, 0, 0, 0]
    (stateAt 0x1000 0x2000)).map
      (fun candidate => (candidate.address, candidate.width, candidate.immediate,
        candidate.operand)) =
    .ok (0x2000, 4, 11, .base .rcx 0) := by rfl

-- A negative disp8 is sign-extended before 64-bit base addition.
example : (check 0x1000 [0xC7, 0x41, 0xFC, 0x2A, 0, 0, 0]
    (stateAt 0x1000 0x2000)).map (fun candidate => candidate.address) =
    .ok 0x1FFC := by rfl

-- mod=00/rm=101 is RIP-relative, rm=100 selects SIB, and REX.W is qword MOV.
example : checkError [0xC7, 0x05, 0, 0, 0, 0, 0x0B, 0, 0, 0] =
    some .unsupportedInstruction := by rfl

example : checkError [0xC7, 0x04, 0x21, 0x0B, 0, 0, 0] =
    some .unsupportedInstruction := by rfl

example : checkError [0x48, 0xC7, 0x01, 0x0B, 0, 0, 0] =
    some .unsupportedInstruction := by rfl

end Grass.Tests.ISA.X86.StoreCandidate
