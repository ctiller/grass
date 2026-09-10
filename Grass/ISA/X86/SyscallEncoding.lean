import Grass.ISA.X86.Decode

/-! The canonical SYSCALL encoding. The opcode row and encoder represent the
instruction; decoding does not certify mode eligibility or privilege transfer.
Intel SDM revision 092, Vol. 2B, SYSCALL (4-698–4-700); AMD APM Vol. 3,
revision 3.38, SYSCALL (484–487). Declaration-level citation enrollment remains
separate from this production-encoder roundtrip. -/

namespace Grass.ISA.X86.SyscallEncoding
open Grass.Std.Logical

/-- The unprefixed `0F 05` production encoding. -/
def encoding : InsnEncoding :=
  { rex := none, escape := true, opcode := 0x05,
    modrm := none, sib := none, disp := .none, imm := .none }

theorem bytes : encoding.toBytes = [0x0F, 0x05] := by decide

/-- `decodes` preserves any trailing bytes after the exact production encoding. -/
theorem decodes (rest : ByteSeq) :
    decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest) := by
  apply decodeInsn_toBytes rest (by rfl)
  · decide
  · decide

end Grass.ISA.X86.SyscallEncoding
