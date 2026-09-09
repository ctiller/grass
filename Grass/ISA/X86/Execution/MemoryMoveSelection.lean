import Grass.ISA.X86.Execution.MemoryMoveNormal

namespace Grass.ISA.X86.Execution.MemoryMoveSelection

open Grass.ISA.X86 MemoryMoveNormal

structure Selection (encoding : InsnEncoding) where
  instruction : Instruction
  encoded : Instruction.Encoding instruction
  encoding_eq : encoded.encoding = encoding

private def displacement? : Displacement → Option (BitVec 32)
  | .d32 bits => some bits
  | _ => none

/-- Reconstruct the bounded RSP/disp32 family, accepting only exact production encodings. -/
def select (encoding : InsnEncoding) : Option (Selection encoding) :=
  match displacement? encoding.disp with
  | none => none
  | some displacement =>
      match encoding.imm with
      | .i32 immediate =>
          let store32 := Instruction.store32Imm displacement immediate
          if h32 : store32.encode? = some encoding then
            some ⟨store32, ⟨encoding, h32⟩, rfl⟩
          else
            let store64 := Instruction.store64SignedImm32 displacement immediate
            if h64 : store64.encode? = some encoding then
              some ⟨store64, ⟨encoding, h64⟩, rfl⟩
            else none
      | .none =>
          match encoding.modrm with
          | none => none
          | some modrm =>
              let high := match encoding.rex with | some rex => rex.r | none => 0
              let destination := Gpr.ofBits high modrm.reg
              let load := Instruction.load32 displacement destination
              if h : load.encode? = some encoding then
                some ⟨load, ⟨encoding, h⟩, rfl⟩
              else none
      | _ => none

theorem encoding_sound {encoding : InsnEncoding} (selected : Selection encoding) :
    selected.instruction.encode? = some encoding := by
  exact selected.encoded.exact.trans (congrArg some selected.encoding_eq)

end Grass.ISA.X86.Execution.MemoryMoveSelection
