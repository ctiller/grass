import Grass.ISA.X86.ImmediateArithmetic

namespace Grass.Tests.ISA.X86.ImmediateArithmetic

open Grass.ISA.X86 Grass.ISA.X86.BasicInstructions Grass.Std.Logical
open Grass.ISA.X86.ImmediateArithmetic

example : (encode .sub .w64 .rsp (.i8 (BitVec.ofInt 8 48))).toBytes =
    [0x48, 0x83, 0xEC, 0x30] := by decide

example : (encode .cmp .w64 .rax (.i8 (BitVec.ofInt 8 (-1)))).toBytes =
    [0x48, 0x83, 0xF8, 0xFF] := by decide

example : (encode .sub .w32 .r12 (.i32 0x12345678)).rex.isSome := by decide

example (kind : Kind) (width : BasicInstructions.Width) (reg : Gpr)
    (immediate : ImmediateArithmetic.Immediate)
    (rest : ByteSeq) :
    decodeInsn ((encode kind width reg immediate).toBytes ++ rest) =
      .ok (encode kind width reg immediate, rest) :=
  decode_encode kind width reg immediate rest

end Grass.Tests.ISA.X86.ImmediateArithmetic
