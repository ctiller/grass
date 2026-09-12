import Tests.ISA.X86.SeamFixtures

/-!
# x86 memory producer seam cases

These are small executable states, built from `Instr.encode` bytes and mapped
regions, for the memory forms introduced at the target seam.  They exercise
`Target.step`, rather than calling `execInstr` directly, so fetching, decoding,
the encoded instruction length, address formation, permissions, and the effect
are one checked path.
-/

namespace Grass.Tests.ISA.X86.SeamMemory

open Grass.ISA.X86
open Grass.ISA.X86.Target
open Grass.Tests.ISA.X86.SeamFixtures

/-- The fixed base form is deliberately always `mod=10` plus SIB.  These
bytes pin the SIB and REX choices for an extended destination and base. -/
def fixedBaseBytes : Bool :=
  encode (.movRM .w64 .r9 .r12 (-16 : BitVec 32)) =
      [0x4D, 0x8B, 0x8C, 0x24, 0xF0, 0xFF, 0xFF, 0xFF] &&
  encode (.movMI32 .w64 .r12 4 (-1 : BitVec 32)) =
      [0x49, 0xC7, 0x84, 0x24, 4, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF] &&
  encode (.leaRM .r9 .r12 4) = [0x4D, 0x8D, 0x8C, 0x24, 4, 0, 0, 0] &&
  encode (.leaRip .r9 4) = [0x4C, 0x8D, 0x0D, 4, 0, 0, 0] &&
  encode (.callRip 4) = [0xFF, 0x15, 4, 0, 0, 0]

/-- Near-miss memory encodings must not silently enter the deliberately narrow
producer vocabulary: LEA is 64-bit here, base forms have no index, and the
group digits select only MOV `/0` and CALL `/2`. -/
def decoderRefusesUnsupportedMemoryForms : Bool :=
  decode [0x8D, 0x84, 0x24, 0, 0, 0, 0] = none &&
  decode [0x4A, 0x8B, 0x84, 0x24, 0, 0, 0, 0] = none &&
  decode [0x48, 0x8B, 0x84, 0x4C, 0, 0, 0, 0] = none &&
  decode [0x48, 0xC7, 0x8C, 0x24, 0, 0, 0, 0, 0, 0, 0, 0] = none &&
  decode [0xFF, 0x1D, 0, 0, 0, 0] = none

def movLoad32ZeroExtends : Bool :=
  let i := Instr.movRM .w32 .r9 .r12 (-16 : BitVec 32)
  let s := withBytes (blankState i (regs [(.r12, 0x210), (.r9, 0xFFFFFFFFFFFFFFFF)])
    [region 0x200 4 true false false]) [(0x200, [0x78, 0x56, 0x34, 0x12])]
  match internal? (step s) with
  | some t => t.reg .r9 == 0x12345678 && t.rip == codeBase + (encode i).length
  | none => false

/-- Negative displacement underflows in 64-bit address arithmetic; it does
not saturate to zero.  LEA isolates that arithmetic from the flat model's
non-wrapping multi-byte region traversal. -/
def negativeDisplacementWraps : Bool :=
  let i := Instr.leaRM .r8 .rax (-2 : BitVec 32)
  let s := blankState i (regs [(.rax, 1)]) []
  match internal? (step s) with
  | some t => t.reg .r8 == 0xFFFFFFFFFFFFFFFF
  | none => false

/-- Positive displacement overflows back to zero in the same arithmetic. -/
def positiveDisplacementWraps : Bool :=
  let i := Instr.leaRM .r8 .rax 1
  let s := blankState i (regs [(.rax, 0xFFFFFFFFFFFFFFFF)]) []
  match internal? (step s) with
  | some t => t.reg .r8 == 0
  | none => false

/-- Loading into the same register that names the base uses the old base for
the address, then replaces that register with the loaded value. -/
def movLoadBaseDestinationAlias : Bool :=
  let i := Instr.movRM .w64 .r12 .r12 0
  let s := withBytes (blankState i (regs [(.r12, 0x300)]) [region 0x300 8 true false false])
    [(0x300, [0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11])]
  match internal? (step s) with
  | some t => t.reg .r12 == 0x1122334455667788
  | none => false

/-- LEA is address arithmetic only, including a destination/base alias and
an extended base; no readable memory is needed at its result. -/
def leaDoesNotReadMemory : Bool :=
  let i := Instr.leaRM .r12 .r12 (-1 : BitVec 32)
  let s := blankState i (regs [(.r12, 0)]) []
  match internal? (step s) with
  | some t => t.reg .r12 == 0xFFFFFFFFFFFFFFFF
  | none => false

/-- RIP-relative addressing begins at the actual fallthrough address. -/
def leaRipUsesFallthrough : Bool :=
  let i := Instr.leaRip .r9 0x20
  let s := blankState i (regs []) []
  match internal? (step s) with
  | some t => (t.reg .r9).toNat == codeBase + (encode i).length + 0x20
  | none => false

def store64SignExtendsImm32 : Bool :=
  let i := Instr.movMI32 .w64 .r12 0 (-1 : BitVec 32)
  let s := blankState i (regs [(.r12, 0x300)]) [region 0x300 8 true true false]
  match internal? (step s) with
  | some t => t.readBytes 0x300 8 = some [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]
  | none => false

def truncatedReadFaults : Bool :=
  let i := Instr.movRM .w64 .r8 .r12 0
  let s := blankState i (regs [(.r12, 0x300)]) [region 0x300 4 true false false]
  isReadFault 0x300 (step s)

def crossPermissionStoreFaults : Bool :=
  let i := Instr.movMI32 .w64 .r12 0 7
  let s := blankState i (regs [(.r12, 0x300)]) [region 0x300 4 true true false]
  isWriteFault 0x300 (step s)

/-- The pointer read precedes the return-slot write even when both name the
same address.  The observed target must be the old pointer, while the slot
holds the actual fallthrough bytes afterwards. -/
def callReadsBeforeAliasedPush : Bool :=
  let i := Instr.callRip 0x2F2
  let slot := 0x3F8
  let before := withBytes
    (blankState i (regs [(.rsp, 0x400)]) [region slot 8 true true false])
    [(slot, [0x77, 0x07, 0, 0, 0, 0, 0, 0])]
  match internal? (step before) with
  | some after => after.rip == 0x777 && (after.reg .rsp).toNat == slot &&
      after.readBytes slot 8 = some [0x06, 0x01, 0, 0, 0, 0, 0, 0]
  | none => false

/-- If both operands are invalid, `call [rip+disp32]` reports its pointer
read failure before considering the unwritable return slot. -/
def callReadFailurePrecedesStackFailure : Bool :=
  let i := Instr.callRip 0xFA
  let s := blankState i (regs [(.rsp, 0)]) []
  isReadFault 0x200 (step s)

/-- Conversely, after a readable pointer has supplied a target, an invalid
return slot is a write failure at the decremented stack address. -/
def callStackFailureAfterReadablePointer : Bool :=
  let i := Instr.callRip 0xFA
  let s := withBytes (blankState i (regs [(.rsp, 0)]) [region 0x200 8 true false false])
    [(0x200, [0x77, 0x07, 0, 0, 0, 0, 0, 0])]
  isWriteFault 0xFFFFFFFFFFFFFFF8 (step s)

def run : IO Unit := do
  expect "fixed base/SIB/REX byte shapes" fixedBaseBytes
  expect "decoder refuses unsupported memory forms" decoderRefusesUnsupportedMemoryForms
  expect "mov r32, [base+negative disp] zero-extends" movLoad32ZeroExtends
  expect "negative displacement wraps at 64 bits" negativeDisplacementWraps
  expect "positive displacement wraps at 64 bits" positiveDisplacementWraps
  expect "mov load base/destination alias" movLoadBaseDestinationAlias
  expect "lea does not read memory" leaDoesNotReadMemory
  expect "lea rip uses the encoded fallthrough" leaRipUsesFallthrough
  expect "mov qword imm32 sign-extends" store64SignExtendsImm32
  expect "truncated readable region faults" truncatedReadFaults
  expect "store crossing permission boundary faults" crossPermissionStoreFaults
  expect "call reads pointer before aliased return push" callReadsBeforeAliasedPush
  expect "call reports pointer read before stack failure" callReadFailurePrecedesStackFailure
  expect "call reports stack write after readable pointer" callStackFailureAfterReadablePointer

end Grass.Tests.ISA.X86.SeamMemory

def main : IO Unit := Grass.Tests.ISA.X86.SeamMemory.run
