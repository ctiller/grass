import Grass.ISA.X86.RegisterSemantics

namespace Grass.Tests.ISA.X86.RegisterSemantics
open Grass.ISA.X86 Grass.ISA.X86.RegisterSemantics

private def initialFlags : Flags Bool := Flags.fromBits 0xAD7

-- Independent known answers distinguish carry, signed overflow, nibble borrow,
-- low-byte parity, unchanged CMP destinations, and undefined logical AF.
example : (evaluate .add .w32 0xFFFFFFFFFFFFFFFF 1 initialFlags).destination 0 = 0 := by decide
example : (evaluate .add .w32 0xFFFFFFFFFFFFFFFF 1 initialFlags).flags.valueBits = 0x55 := by decide
example : (evaluate .sub .w32 0 1 initialFlags).flags.valueBits = 0x95 := by decide
example : (evaluate .add .w32 0x7FFFFFFF 1 initialFlags).flags.valueBits = 0x894 := by decide
example : (evaluate .sub .w32 0x80000000 1 initialFlags).flags.valueBits = 0x814 := by decide
example : (evaluate .add .w64 0x7FFFFFFFFFFFFFFF 1 initialFlags).flags.valueBits = 0x894 := by decide
example : (evaluate .sub .w64 0x8000000000000000 1 initialFlags).flags.valueBits = 0x814 := by decide
example : (evaluate .cmp .w32 0xFFFFFFFF00000001 1 initialFlags).destination
    0xFFFFFFFF00000001 = 0xFFFFFFFF00000001 := by decide
example : (evaluate .cmp .w32 0xFFFFFFFF00000001 1 initialFlags).flags.valueBits = 0x44 := by decide
example : (evaluate .test .w32 0 0 initialFlags).flags.definedMask = 0x8C5 := by decide
example : (evaluate .test .w32 0 0 initialFlags).flags.valueBits = 0x44 := by decide
example : (evaluate .xor .w32 0xFFFFFFFF00000001 1 initialFlags).write = some 0 := by decide
example : (evaluate .test .w32 0 0 initialFlags).flags.Allows ⟨false,true,false,true,false,false⟩ := by decide
example : (evaluate .test .w32 0 0 initialFlags).flags.Allows ⟨false,true,true,true,false,false⟩ := by decide
example : ¬ (evaluate .test .w32 0 0 initialFlags).flags.Allows ⟨true,true,true,true,false,false⟩ := by decide
example : (evaluate .cmp .w32 1 0 initialFlags).flags.above? = some true := by decide
example : (evaluate .cmp .w32 0 1 initialFlags).flags.above? = some false := by decide
example : (evaluate .cmp .w32 1 1 initialFlags).flags.equal? = some true := by decide
example : (evaluateImmediate .sub .w64 0 (.i8 255) initialFlags).write = some 1 := by decide
example : (evaluateImmediate .cmp .w64 0 (.i32 0xFFFFFFFF) initialFlags).flags.cf = some true := by decide

-- The real loop's aliasing TEST must not write or zero-extend EAX.
private def testLoop : Instruction := ⟨.test,.w32,.rax,.rax⟩
example : testLoop.registersAfter (fun _ => 0xFFFFFFFF00000000) initialFlags .rax =
    0xFFFFFFFF00000000 := by decide
example : (testLoop.effect (fun _ => 0xFFFFFFFF00000000) initialFlags).flags.equal? = some true := by decide

end Grass.Tests.ISA.X86.RegisterSemantics
