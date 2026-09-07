import Grass.Grammar.Realization

/-!
# Whole-input parsing

`requireWhole` turns a selected prefix parse with residual bytes into the
distinct `ParseError.trailingInput` classification. `ParserRealizes.whole`
proves the adapter realizes `FormatSemantics.whole`.
-/

namespace Grass.Grammar

open Grass.Std.Logical

/-- Restrict prefix semantics to selected derivations consuming the complete
input, while retaining the underlying incomplete and invalid classifications. -/
def FormatSemantics.whole {α : Type} {format : Format α}
    (semantics : FormatSemantics format) : FormatSemantics format where
  selectedDerivation input value rest :=
    rest = Vec.empty ∧ semantics.selectedDerivation input value rest
  repairableIncompletePrefix := semantics.repairableIncompletePrefix
  irrecoverablyInvalidPrefix input error :=
    semantics.irrecoverablyInvalidPrefix input error ∨
      (error = .trailingInput ∧
        ∃ value rest, semantics.selectedDerivation input value rest ∧ rest ≠ Vec.empty)
  selectedSound := by
    intro input value rest selected
    exact semantics.selectedSound selected.2

/-- Require a finite parser to consume its complete input. -/
def requireWhole {α : Type}
    (parse : Std.Logical.ByteArray → ParseResult α)
    (input : Std.Logical.ByteArray) : ParseResult α :=
  match parse input with
  | .done value rest =>
      if rest = Vec.empty then .done value Vec.empty
      else .invalid .trailingInput
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- `requireWhole` preserves the finite parser's incomplete result exactly. -/
theorem requireWhole_eq_needMore_iff {α : Type}
    (parse : Std.Logical.ByteArray → ParseResult α)
    (input : Std.Logical.ByteArray) (hint : Option Nat) :
    requireWhole parse input = .needMore hint ↔ parse input = .needMore hint := by
  unfold requireWhole
  cases result : parse input with
  | done value rest =>
      by_cases empty : rest = Vec.empty <;> simp [empty]
  | needMore actual => simp
  | invalid error => simp

/-- Operationally, whole-input invalidity is either inherited or is an
otherwise successful parse with a nonempty suffix. -/
theorem requireWhole_eq_invalid_iff {α : Type}
    (parse : Std.Logical.ByteArray → ParseResult α)
    (input : Std.Logical.ByteArray) (error : ParseError) :
    requireWhole parse input = .invalid error ↔
      parse input = .invalid error ∨
        (error = .trailingInput ∧
          ∃ value rest, parse input = .done value rest ∧ rest ≠ Vec.empty) := by
  unfold requireWhole
  cases result : parse input with
  | done value rest =>
      by_cases empty : rest = Vec.empty
      · simp [empty]
      · simp [empty]
        constructor
        · intro sameError
          exact ⟨sameError.symm, value, rest, ⟨rfl, rfl⟩, empty⟩
        · rintro ⟨sameError, _⟩
          exact sameError.symm
  | needMore hint => simp
  | invalid actual => simp

/-- `ParserRealizes.whole` preserves the full parser-realization contract and
proves the exact trailing-input classification in `FormatSemantics.whole`. -/
theorem ParserRealizes.whole {α : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    (parser : ParserRealizes semantics parse) :
    ParserRealizes semantics.whole (requireWhole parse) where
  successSound input value rest success := by
    unfold requireWhole at success
    cases parsed : parse input with
    | done parsedValue parsedRest =>
        by_cases empty : parsedRest = Vec.empty
        · simp [parsed, empty] at success
          rcases success with ⟨rfl, rfl⟩
          exact parser.successSound input parsedValue Vec.empty (by simpa [empty] using parsed)
        · simp [parsed, empty] at success
    | needMore hint => simp [parsed] at success
    | invalid error => simp [parsed] at success
  successComplete input value rest selected := by
    rcases selected with ⟨restEmpty, selected⟩
    subst rest
    simp [requireWhole, parser.successComplete input value Vec.empty selected]
  needMoreExact input hint := by
    rw [requireWhole_eq_needMore_iff, parser.needMoreExact]
    rfl
  invalidExact input error := by
    rw [requireWhole_eq_invalid_iff, parser.invalidExact]
    constructor
    · intro invalid
      rcases invalid with inherited | ⟨trailing, value, rest, success, nonempty⟩
      · exact Or.inl inherited
      · exact Or.inr ⟨trailing, value, rest, parser.consumes input value rest success, nonempty⟩
    · intro invalid
      rcases invalid with inherited | ⟨trailing, value, rest, selected, nonempty⟩
      · exact Or.inl inherited
      · exact Or.inr ⟨trailing, value, rest,
          parser.successComplete input value rest selected, nonempty⟩
  consumes input value rest success := by
    unfold requireWhole at success
    cases parsed : parse input with
    | done parsedValue parsedRest =>
        by_cases empty : parsedRest = Vec.empty
        · simp [parsed, empty] at success
          rcases success with ⟨rfl, rfl⟩
          exact ⟨rfl, parser.consumes input parsedValue Vec.empty (by simpa [empty] using parsed)⟩
        · simp [parsed, empty] at success
    | needMore hint => simp [parsed] at success
    | invalid error => simp [parsed] at success

end Grass.Grammar
