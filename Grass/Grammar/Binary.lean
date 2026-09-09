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

/-- Repetition of the unconstrained byte format consumes exactly the returned
byte sequence and no other prefix. -/
theorem derives_repeatedBytes_iff {count : Nat}
    {input value rest : Std.Logical.ByteArray} :
    Derives (repeatedBytesFormat count) input value rest ↔
      input = value ++ rest ∧ value.length = count := by
  constructor
  · intro derivation
    induction count generalizing input value with
    | zero =>
        have shape := derivation.repeatOuterShape
        rcases shape with ⟨rfl, rfl⟩
        simp
    | succ count inductionHypothesis =>
        have shape := derivation.repeatOuterShape
        rcases shape with ⟨middle, head, tail, rfl, headDerivation, tailDerivation⟩
        have headInput := headDerivation.byteInput
        have tailParts := inductionHypothesis tailDerivation
        constructor
        · rw [headInput, tailParts.1]
          simp [Vec.append_assoc]
        · simp [tailParts.2]
          omega
  · rintro ⟨rfl, rfl⟩
    exact anyBytes_derives value rest

/-- Exact fixed-width parsing selects the leading `count` bytes, classifies
short buffers by their exact deficit, and has no irrecoverably invalid prefix. -/
def fixedBytesSemantics (count : Nat) : FormatSemantics (fixedBytesFormat count) where
  selectedDerivation input value rest :=
    input = value.1 ++ rest
  selectionPolicy input value rest := input = value.1 ++ rest
  repairableIncompletePrefix input hint :=
    input.length < count ∧ hint = some (count - input.length)
  irrecoverablyInvalidPrefix _ _ := False
  selectedIff := by
    intro input value rest
    constructor
    · intro selected
      subst input
      exact ⟨Derives.lift (by
        simpa [value.2] using anyBytes_derives value.1 rest), rfl⟩
    · rintro ⟨_derivation, policy⟩
      exact policy
  selectedComplete := by
    rintro input ⟨_value, rest, derivation⟩
    have itemLength : ∀ {itemInput itemValue itemRest},
        Derives anyByteFormat itemInput itemValue itemRest →
          itemInput.length = 1 + itemRest.length := by
      intro itemInput itemValue itemRest itemDerivation
      rw [itemDerivation.byteInput]
      simp
    have consumed := derivation.lift_inner.repeatConsumedLengthShape 1 itemLength
    have enough : count ≤ input.length := by
      simp at consumed
      omega
    let value : SizedByteArray count :=
      ⟨input.take count, by simp [enough]⟩
    exact ⟨value, input.drop count, by simp [value]⟩
  selectedDeterministic := by
    intro input value₁ rest₁ value₂ rest₂ first second
    rw [first] at second
    have values : value₁.1 = value₂.1 := by
      have taken := congrArg (fun bytes => bytes.take count) second
      simpa [Vec.take_append_of_length_eq, value₁.2, value₂.2] using taken
    have rests : rest₁ = rest₂ := by
      have dropped := congrArg (fun bytes => bytes.drop count) second
      simpa [Vec.drop_append_of_length_eq, value₁.2, value₂.2] using dropped
    exact ⟨SizedVec.ext values, rests⟩
  repairableNoSelection := by
    rintro input hint ⟨short, _⟩ ⟨value, rest, selected⟩
    have lengths := congrArg Vec.length selected
    simp [Vec.length_append, value.2] at lengths
    omega
  repairableHasCompletion := by
    rintro input hint ⟨short, _⟩
    let suffix := Vec.replicate (count - input.length) (0 : Byte)
    have totalLength : (input ++ suffix).length = count := by
      simp [suffix, Vec.length_append]
      omega
    let value : SizedByteArray count := ⟨input ++ suffix, totalLength⟩
    exact ⟨suffix, value, Vec.empty, by simp [value]⟩
  repairableHintExact := by
    rintro input minimumAdditional ⟨short, hintEquality⟩
    have minimumEquality : minimumAdditional = count - input.length :=
      Option.some.inj hintEquality
    subst minimumAdditional
    let suffix := Vec.replicate (count - input.length) (0 : Byte)
    have totalLength : (input ++ suffix).length = count := by
      simp [suffix, Vec.length_append]
      omega
    let value : SizedByteArray count := ⟨input ++ suffix, totalLength⟩
    exact ⟨suffix, value, Vec.empty, by simp [suffix, value]⟩
  repairableHintMinimal := by
    rintro input minimumAdditional ⟨short, hintEquality⟩ candidate
      ⟨suffix, value, rest, suffixLength, selected⟩
    have minimumEquality : minimumAdditional = count - input.length :=
      Option.some.inj hintEquality
    subst minimumAdditional
    have lengths := congrArg Vec.length selected
    simp [Vec.length_append, value.2, suffixLength] at lengths
    omega
  repairableHintUnique := by
    rintro input first second ⟨_, rfl⟩ ⟨_, rfl⟩
    rfl
  repairableComplete := by
    intro input noSelection _completion
    have short : input.length < count := by
      by_cases isShort : input.length < count
      · exact isShort
      · have enough : count ≤ input.length := Nat.le_of_not_gt isShort
        exfalso
        apply noSelection
        let value : SizedByteArray count :=
          ⟨input.take count, by simp [enough]⟩
        exact ⟨value, input.drop count, by simp [value]⟩
    exact ⟨some (count - input.length), short, rfl⟩
  invalidNoCompletion := by simp
  invalidClassUnique := by simp
  invalidComplete := by
    intro input noCompletion
    exfalso
    by_cases short : input.length < count
    · apply noCompletion
      let suffix := Vec.replicate (count - input.length) (0 : Byte)
      have totalLength : (input ++ suffix).length = count := by
        simp [suffix, Vec.length_append]
        omega
      let value : SizedByteArray count := ⟨input ++ suffix, totalLength⟩
      exact ⟨suffix, value, Vec.empty, by simp [value]⟩
    · apply noCompletion
      have enough : count ≤ input.length := Nat.le_of_not_gt short
      let value : SizedByteArray count :=
        ⟨input.take count, by simp [enough]⟩
      exact ⟨Vec.empty, value, input.drop count, by simp [value]⟩

end Grass.Grammar
