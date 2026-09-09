import Grass.ISA.X86.Rel32

namespace Grass.Tests.ISA.X86.Rel32

open Grass.ISA.X86 Grass.ISA.X86.Rel32 Grass.Std.Logical

def signedMinimum : BitVec 32 := BitVec.ofInt 32 (-(2^31 : Int))
def signedMaximum : BitVec 32 := BitVec.ofInt 32 ((2^31 : Int) - 1)

example : (encode .jump signedMinimum).toBytes = [0xE9, 0x00, 0x00, 0x00, 0x80] := by decide
example : (encode .jump signedMaximum).toBytes = [0xE9, 0xFF, 0xFF, 0xFF, 0x7F] := by decide
example : (encode .equal 0).toBytes = [0x0F, 0x84, 0x00, 0x00, 0x00, 0x00] := by decide
example : (encode .above 1).toBytes = [0x0F, 0x87, 0x01, 0x00, 0x00, 0x00] := by decide

example : encodedSize .jump = 5 ∧ encodedSize .equal = 6 ∧ encodedSize .above = 6 := by decide

theorem every_rel32_encoding_roundtrips (kind : Kind) (bits : BitVec 32) (rest : ByteSeq) :
    decodeInsn ((encode kind bits).toBytes ++ rest) = .ok (encode kind bits, rest) :=
  decode_encode kind bits rest

end Grass.Tests.ISA.X86.Rel32
