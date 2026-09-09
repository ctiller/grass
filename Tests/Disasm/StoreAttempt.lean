import Grass.Disasm.StoreAttempt

namespace Grass.Tests.Disasm.StoreAttempt

open Grass.Core Grass.Std.Logical Grass.Disasm.StoreAttempt Grass.ISA.X86
  Grass.ISA.X86.Execution

private def machine : Grass.Memory.MachineState :=
  Grass.Memory.MachineState.initial .empty

private def stateAt (rip rcx : BitVec 64) : State :=
  { machine := machine
    gpr := fun register => if register = .rcx then rcx else 0
    rip := rip
    rflags := 0 }

def safeBytes : ByteSeq := [0xC7, 0x41, 0x04, 0x2A, 0, 0, 0, 0xC3]
def oobBytes : ByteSeq := [0xC7, 0x41, 0x08, 0x2A, 0, 0, 0, 0xC3]

private def checkError (rip : BitVec 64) (bytes : ByteSeq) (state : State) : Option Error :=
  match check rip bytes state with
  | .error error => some error
  | .ok _ => none

-- Both corpus functions expose their decoded store candidate even though only the
-- caller's object contract can classify the second footprint as out of bounds.
example : (check 0x140001000 safeBytes (stateAt 0x140001000 0x2000)).map
    (fun evidence => (evidence.base, evidence.address, evidence.width, evidence.immediate)) =
    .ok (.rcx, 0x2004, 4, 42) := by rfl

example : (check 0x140001000 oobBytes (stateAt 0x140001000 0x2000)).map
    (fun evidence => (evidence.base, evidence.address, evidence.width, evidence.immediate)) =
    .ok (.rcx, 0x2008, 4, 42) := by rfl

-- Exact decoded bytes include the following RET as the retained suffix.
example : (check 0x140001000 safeBytes (stateAt 0x140001000 0x2000)).map
    (fun evidence => evidence.site.rest) = .ok [0xC3] := by rfl

-- A mismatching RIP is rejected. An arbitrary state with the same RIP still
-- needs independently established reached-state and caller-contract evidence.
example : (check 0x140001000 safeBytes (stateAt 0x140001001 0x2000)).map
    (fun evidence => evidence.address) = .error .stateRipMismatch := by rfl

-- A signed disp8 is sign-extended through the production addressing decoder.
example : (check 0x140001000 [0xC7, 0x41, 0xFC, 0x2A, 0, 0, 0, 0xC3]
    (stateAt 0x140001000 0x2000)).map (fun evidence => evidence.address) =
    .ok 0x1FFC := by rfl

-- REX.W selects the qword form, `/1` is not MOV, and rm=100 selects a SIB.
example : checkError 0x1000 [0x48, 0xC7, 0x41, 4, 42, 0, 0, 0]
    (stateAt 0x1000 0x2000) = some .unsupportedInstruction := by rfl

example : checkError 0x1000 [0xC7, 0x49, 4, 42, 0, 0, 0]
    (stateAt 0x1000 0x2000) = some .unsupportedInstruction := by rfl

example : checkError 0x1000 [0xC7, 0x44, 0x21, 4, 42, 0, 0, 0]
    (stateAt 0x1000 0x2000) = some .unsupportedInstruction := by rfl

-- The decoded address exists, but its four-byte linear footprint would wrap.
example : checkError 0x1000 [0xC7, 0x41, 0, 42, 0, 0, 0]
    (stateAt 0x1000 0xFFFFFFFFFFFFFFFE) = some .addressWrap := by rfl

end Grass.Tests.Disasm.StoreAttempt
