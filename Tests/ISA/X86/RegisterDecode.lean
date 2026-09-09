import Grass.ISA.X86.RegisterDecode

/-! Bounded coverage for canonical semantic register decoding. -/
namespace Grass.Tests.ISA.X86.RegisterDecode

open Grass.ISA.X86 Grass.ISA.X86.BasicInstructions
open Grass.ISA.X86.RegisterSemantics Grass.ISA.X86.RegisterDecode

def suffix : Grass.Std.Logical.ByteSeq := [0xAA, 0x55]

def decodeView (bytes : Grass.Std.Logical.ByteSeq) :
    Option (RegisterSemantics.Instruction × Grass.Std.Logical.ByteSeq) :=
  match decode bytes with
  | .error _ => Option.none
  | .ok result => some (result.instruction, result.rest)

def canonicalPair (kind : Kind) (width : BasicInstructions.Width)
    (destination source : Gpr) : Bool :=
  let instruction : RegisterSemantics.Instruction :=
    ⟨kind, width, destination, source⟩
  (select instruction.encoding).map (fun selected => selected.instruction) ==
      some instruction &&
    decodeView (instruction.encoding.toBytes ++ suffix) == some (instruction, suffix)

def canonicalFamily (kind : Kind) (width : BasicInstructions.Width) : Bool :=
  Gpr.all.all fun destination =>
    Gpr.all.all fun source => canonicalPair kind width destination source

theorem mov_all_registers :
    canonicalFamily .mov .w32 && canonicalFamily .mov .w64 := by decide

theorem add_all_registers :
    canonicalFamily .add .w32 && canonicalFamily .add .w64 := by decide

theorem sub_all_registers :
    canonicalFamily .sub .w32 && canonicalFamily .sub .w64 := by decide

theorem cmp_all_registers :
    canonicalFamily .cmp .w32 && canonicalFamily .cmp .w64 := by decide

theorem test_all_registers :
    canonicalFamily .test .w32 && canonicalFamily .test .w64 := by decide

set_option maxHeartbeats 400000 in
theorem xor_all_registers :
    canonicalFamily .xor .w32 && canonicalFamily .xor .w64 := by decide

def errorView (bytes : Grass.Std.Logical.ByteSeq) : Option Error :=
  match decode bytes with
  | .error error => some error
  | .ok _ => Option.none

theorem truncated_is_decode_error :
    errorView [] = some (.decode (.truncated "opcode or REX prefix")) := by decide

theorem push_is_explicitly_unsupported :
    errorView (push .rax).toBytes = some (.unsupported (push .rax)) := by decide

def redundantRexMov : InsnEncoding :=
  { (movRegReg .w32 .rax .rbx) with rex := some Rex.bare }

theorem redundant_rex_decodes :
    decodeInsn redundantRexMov.toBytes = .ok (redundantRexMov, []) := by rfl

theorem redundant_rex_is_noncanonical :
    errorView redundantRexMov.toBytes = some (.unsupported redundantRexMov) := by decide

end Grass.Tests.ISA.X86.RegisterDecode
