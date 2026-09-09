import Grass.ISA.X86.Execution.StoreCandidate

/-! Compatibility names for the x86-owned decoded `[base]` and
`[base+disp8]` store-candidate model. -/
namespace Grass.Disasm.StoreAttempt

open Grass.Std.Logical Grass.ISA.X86 Grass.ISA.X86.Execution

abbrev Error := StoreCandidate.Error
abbrev Evidence := StoreCandidate.Evidence

namespace Evidence

def operand {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) : MemOperand := StoreCandidate.Evidence.operand e

theorem decodedMemory_operand {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) :
    decodeMem
      { mod := e.displacement.modBits, rm := e.base.encodingBits, sib := none
        disp := e.displacement.encoded, rexX := 0, rexB := 0 } = some e.operand :=
  StoreCandidate.Evidence.decodedMemory_operand e

theorem productionEncoder_accepts {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) :
    (movMem32Imm32 e.operand e.immediate).isSome :=
  StoreCandidate.Evidence.productionEncoder_accepts e

def productionEncoding {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) : InsnEncoding := StoreCandidate.Evidence.productionEncoding e

theorem productionEncoding_eq {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) :
    movMem32Imm32 e.operand e.immediate = some e.productionEncoding :=
  StoreCandidate.Evidence.productionEncoding_eq e

theorem productionEncoding_decodes {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) (rest : ByteSeq) :
    decodeInsn (e.productionEncoding.toBytes ++ rest) =
      .ok (e.productionEncoding, rest) :=
  StoreCandidate.Evidence.productionEncoding_decodes e rest

def address {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) : BitVec 64 := StoreCandidate.Evidence.address e

def width {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) : Nat := StoreCandidate.Evidence.width e

@[simp] theorem width_eq {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) : e.width = 4 := StoreCandidate.Evidence.width_eq e

theorem footprint_noWrap {rip : BitVec 64} {bytes : ByteSeq} {state : State}
    (e : Evidence rip bytes state) : e.address.toNat + e.width ≤ 2 ^ 64 :=
  StoreCandidate.Evidence.footprint_noWrap e

end Evidence

abbrev check := StoreCandidate.check

end Grass.Disasm.StoreAttempt
