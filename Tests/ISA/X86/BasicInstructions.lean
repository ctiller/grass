import Grass.ISA.X86.BasicInstructions

/-! Golden shapes and public decoder roundtrips for the bounded constructors. -/
namespace Grass.Tests.ISA.X86.BasicInstructions

open Grass.Core Grass.ISA.X86 Grass.ISA.X86.BasicInstructions

theorem push_extended_golden : (push .r12).toBytes = [0x41, 0x54] := by decide

theorem mov64_golden :
    (movRegReg .w64 .rax .rbx).toBytes = [0x48, 0x89, 0xD8] := by decide

theorem mov32_extended_golden :
    (movRegReg .w32 .rax .r9).toBytes = [0x44, 0x89, 0xC8] := by decide

def memoryMov := movReg32Mem .r9 (.base .rsp 0x11223344)

theorem mov32_memory_golden :
    memoryMov.map InsnEncoding.toBytes =
      some [0x44, 0x8B, 0x8C, 0x24, 0x44, 0x33, 0x22, 0x11] := by decide

theorem arithmetic_golden :
    (testRegReg .w64 .rax .rbx).toBytes = [0x48, 0x85, 0xD8] ∧
    (cmpRegReg .w64 .rax .rbx).toBytes = [0x48, 0x39, 0xD8] ∧
    (addRegReg .w64 .rax .rbx).toBytes = [0x48, 0x01, 0xD8] ∧
    (subRegReg .w64 .rax .rbx).toBytes = [0x48, 0x29, 0xD8] ∧
    (xorRegReg .w64 .rax .rbx).toBytes = [0x48, 0x31, 0xD8] := by decide

theorem ud2_golden : ud2.toBytes = [0x0F, 0x0B] := by decide

theorem representative_roundtrips :
    decodeInsn (push .r12).toBytes = .ok (push .r12, []) ∧
    decodeInsn (movRegReg .w32 .r8 .r15).toBytes =
      .ok (movRegReg .w32 .r8 .r15, []) ∧
    decodeInsn (xorRegReg .w64 .r13 .r14).toBytes =
      .ok (xorRegReg .w64 .r13 .r14, []) ∧
    decodeInsn ud2.toBytes = .ok (ud2, []) := by
  exact ⟨by simpa using push_decodes .r12 [],
    by simpa using movRegReg_decodes .w32 .r8 .r15 [],
    by simpa using xorRegReg_decodes .w64 .r13 .r14 [],
    by simpa using ud2_decodes []⟩

end Grass.Tests.ISA.X86.BasicInstructions
