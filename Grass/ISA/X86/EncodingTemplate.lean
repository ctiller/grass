import Grass.ISA.X86.Decode

/-! A reusable proof boundary between an instruction constructor and one exact
registered decoder-table row per operand. This layer states encoding facts only;
it assigns no execution effects or operand semantics. -/
namespace Grass.ISA.X86

open Grass.Std.Logical

structure EncodingTemplate (Operand : Type) where
  encode : Operand → InsnEncoding
  spec : Operand → OpcodeSpec
  registered : ∀ operand,
    findSpec (spec operand).escape (spec operand).opcode = some (spec operand)
  matchesSpec : ∀ operand, MatchesSpec (encode operand) (spec operand)
  wellFormed : ∀ operand, (encode operand).WellFormed

namespace EncodingTemplate

variable {Operand : Type} (template : EncodingTemplate Operand)

theorem decode_encode (operand : Operand) (rest : ByteSeq) :
    decodeInsn ((template.encode operand).toBytes ++ rest) =
      .ok (template.encode operand, rest) := by
  have agreement := template.matchesSpec operand
  apply decodeInsn_toBytes (s := template.spec operand) rest
  · simpa [agreement.1, agreement.2.1] using template.registered operand
  · exact agreement
  · exact template.wellFormed operand

theorem bytes_length (operand : Operand) :
    (template.encode operand).toBytes.length = (template.encode operand).size :=
  InsnEncoding.length_toBytes _

end EncodingTemplate
end Grass.ISA.X86
