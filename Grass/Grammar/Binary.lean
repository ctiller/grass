import Grass.Grammar.Realization

/-!
# Derived binary formats

This module builds format descriptions from the generic grammar algebra. It
contains no executable reader and no instruction-set encoding fact.
-/

namespace Grass.Grammar

open Grass.Std.Logical

/-- A fixed-width sequence of unconstrained bytes. -/
def fixedBytesFormat (count : Nat) : Format Std.Logical.ByteArray :=
  .repeat count anyByteFormat

/-- Every logical byte sequence derives from a repetition whose count is its
length, preserving an arbitrary suffix exactly. -/
theorem anyBytes_derives (value rest : Std.Logical.ByteArray) :
    Derives (fixedBytesFormat value.length) (value ++ rest) value rest := by
  induction value using Vec.recOnCons with
  | empty => exact Derives.repeatZero anyByteFormat rest
  | cons byte tail tailDerivation =>
      simpa [fixedBytesFormat, anyByteFormat, Vec.append_assoc, Nat.add_comm] using
        Derives.repeatSucc
          (Derives.byte (fun _ => True) byte (tail ++ rest) trivial)
          tailDerivation

/-- Exact fixed-width parsing selects the leading `count` bytes, classifies
short buffers by their exact deficit, and has no irrecoverably invalid prefix. -/
def fixedBytesSemantics (count : Nat) : FormatSemantics (fixedBytesFormat count) where
  selectedDerivation input value rest :=
    input = value ++ rest ∧ value.length = count
  repairableIncompletePrefix input hint :=
    input.length < count ∧ hint = some (count - input.length)
  irrecoverablyInvalidPrefix _ _ := False
  selectedSound := by
    intro input value rest selected
    obtain ⟨inputEq, lengthEq⟩ := selected
    subst input
    simpa [lengthEq] using anyBytes_derives value rest

end Grass.Grammar
