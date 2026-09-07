import Grass.Grammar.Realization

/-!
# Derived binary formats

This module builds format descriptions from the generic grammar algebra. It
contains no executable reader and no instruction-set encoding fact.
-/

namespace Grass.Grammar

open Grass.Std.Logical

/-- A logical vector paired with proof that its length is exactly `count`.
Equality is inherited from the underlying `Vec`; the proof field is irrelevant. -/
abbrev SizedVec (α : Type) (count : Nat) :=
  {value : Vec α // value.length = count}

namespace SizedVec

/-- Sized vectors are equal exactly when their underlying logical vectors are;
length proofs carry no additional identity. -/
@[ext] theorem ext {α : Type} {count : Nat}
    {left right : SizedVec α count} (values : left.1 = right.1) : left = right :=
  Subtype.ext values

/-- The length retained by every sized vector. -/
@[simp] theorem length {α : Type} {count : Nat} (value : SizedVec α count) :
    value.1.length = count :=
  value.2

instance {α : Type} {count : Nat} [DecidableEq α] :
    DecidableEq (SizedVec α count) := fun left right =>
  decidable_of_iff (left.1 = right.1)
    ⟨Subtype.ext, fun equal => congrArg Subtype.val equal⟩

instance {α : Type} {count : Nat} [Repr α] : Repr (SizedVec α count) where
  reprPrec value prec := reprPrec value.1 prec

end SizedVec

/-- A fixed-width value over Grass's sole logical byte container. -/
abbrev SizedByteArray (count : Nat) := SizedVec Byte count

/-- The unsized repeated-byte language used beneath `fixedBytesFormat`. -/
def repeatedBytesFormat (count : Nat) : Format Std.Logical.ByteArray :=
  .repeat count anyByteFormat

/-- A fixed-width sequence whose exact length is present in its value type. -/
def fixedBytesFormat (count : Nat) : Format (SizedByteArray count) :=
  (repeatedBytesFormat count).refineValue fun value => value.length = count

/-- The sized format derives exactly when its underlying repeated-byte format
derives the same logical byte vector. -/
theorem derives_fixedBytes_iff {count : Nat} {input rest : Std.Logical.ByteArray}
    {value : SizedByteArray count} :
    Derives (fixedBytesFormat count) input value rest ↔
      Derives (repeatedBytesFormat count) input value.1 rest := by
  simpa [fixedBytesFormat] using
    (derives_refineValue_iff
      (inner := repeatedBytesFormat count)
      (accepts := fun bytes : Std.Logical.ByteArray => bytes.length = count)
      (value := value.1) value.2)

/-- Every logical byte sequence derives from a repetition whose count is its
length, preserving an arbitrary suffix exactly. -/
theorem anyBytes_derives (value rest : Std.Logical.ByteArray) :
    Derives (repeatedBytesFormat value.length) (value ++ rest) value rest := by
  induction value using Vec.recOnCons with
  | empty => exact Derives.repeatZero anyByteFormat rest
  | cons byte tail tailDerivation =>
      simpa [repeatedBytesFormat, anyByteFormat, Vec.append_assoc, Nat.add_comm] using
        Derives.repeatSucc
          (Derives.byte (fun _ => True) byte (tail ++ rest) trivial)
          tailDerivation

/-- Exact fixed-width parsing selects the leading `count` bytes, classifies
short buffers by their exact deficit, and has no irrecoverably invalid prefix. -/
def fixedBytesSemantics (count : Nat) : FormatSemantics (fixedBytesFormat count) where
  selectedDerivation input value rest :=
    input = value.1 ++ rest
  repairableIncompletePrefix input hint :=
    input.length < count ∧ hint = some (count - input.length)
  irrecoverablyInvalidPrefix _ _ := False
  selectedSound := by
    intro input value rest selected
    subst input
    exact Derives.lift (by
      simpa [value.2] using anyBytes_derives value.1 rest)

end Grass.Grammar
