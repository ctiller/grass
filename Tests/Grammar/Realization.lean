import Grass.Grammar.Realization

/-! # Parser/writer realization fixtures -/

namespace Grass.Tests.Grammar

open Grass.Std.Logical Grass.Grammar

example (value : Byte) (rest : Std.Logical.ByteArray) :
    anyByteSemantics.selectedDerivation
      (Vec.singleton value ++ rest) value rest := rfl

example : anyByteSemantics.repairableIncompletePrefix Vec.empty (some 1) :=
  ⟨rfl, rfl⟩

example (error : ParseErrorClass) :
    ¬ anyByteSemantics.irrecoverablyInvalidPrefix Vec.empty error := by
  simp [anyByteSemantics]

example (input : Std.Logical.ByteArray) :
    HasSelection anyByteSemantics.selectedDerivation input ∨
      (∃ hint, anyByteSemantics.repairableIncompletePrefix input hint) ∨
      (∃ errorClass,
        anyByteSemantics.irrecoverablyInvalidPrefix input errorClass) :=
  anyByteSemantics.classifies input

def rejectAllParser (_ : Std.Logical.ByteArray) : ParseResult Byte :=
  .invalid (.malformed "reject all")

/-- No lawful semantics for `anyByteFormat` can make a reject-all parser a
realization, because every one-byte input has a derivation that must be selected. -/
theorem rejectAllParser_not_realizable :
    ¬∃ semantics : FormatSemantics anyByteFormat,
      ParserRealizes semantics rejectAllParser := by
  rintro ⟨semantics, parser⟩
  have derivation : Derives anyByteFormat (Vec.singleton 0) 0 Vec.empty :=
    Derives.byte (fun _ => True) 0 Vec.empty trivial
  obtain ⟨value, rest, selected⟩ :=
    semantics.selectedComplete ⟨0, Vec.empty, derivation⟩
  have success := parser.successComplete (Vec.singleton 0) value rest selected
  simp [rejectAllParser] at success

def acceptOnlyZeroParser (input : Std.Logical.ByteArray) : ParseResult Byte :=
  if input = Vec.singleton 0 then .done 0 Vec.empty
  else .invalid (.malformed "not zero")

/-- A parser cannot realize `anyByteFormat` by accepting only one valid byte. -/
theorem acceptOnlyZeroParser_not_realizable :
    ¬∃ semantics : FormatSemantics anyByteFormat,
      ParserRealizes semantics acceptOnlyZeroParser := by
  rintro ⟨semantics, parser⟩
  have derivation : Derives anyByteFormat (Vec.singleton 1) 1 Vec.empty :=
    Derives.byte (fun _ => True) 1 Vec.empty trivial
  obtain ⟨value, rest, selected⟩ :=
    semantics.selectedComplete ⟨1, Vec.empty, derivation⟩
  have success := parser.successComplete (Vec.singleton 1) value rest selected
  have unequal : (Vec.singleton (1 : Byte)) ≠ Vec.singleton 0 := by decide
  rw [acceptOnlyZeroParser, if_neg unequal] at success
  cases success

def falseNeedMoreParser (_ : Std.Logical.ByteArray) : ParseResult Byte :=
  .needMore none

/-- A parser cannot classify already valid bytes as incomplete. -/
theorem falseNeedMoreParser_not_realizable :
    ¬∃ semantics : FormatSemantics anyByteFormat,
      ParserRealizes semantics falseNeedMoreParser := by
  rintro ⟨semantics, parser⟩
  have derivation : Derives anyByteFormat (Vec.singleton 0) 0 Vec.empty :=
    Derives.byte (fun _ => True) 0 Vec.empty trivial
  obtain ⟨value, rest, selected⟩ :=
    semantics.selectedComplete ⟨0, Vec.empty, derivation⟩
  have success := parser.successComplete (Vec.singleton 0) value rest selected
  simp [falseNeedMoreParser] at success

def truncationAsInvalidParser (input : Std.Logical.ByteArray) : ParseResult Byte :=
  match input.get? 0 with
  | none => .invalid (.malformed "empty")
  | some value => .done value (input.drop 1)

/-- A repairable empty prefix cannot be classified as irrecoverably invalid. -/
theorem truncationAsInvalidParser_not_realizable :
    ¬∃ semantics : FormatSemantics anyByteFormat,
      ParserRealizes semantics truncationAsInvalidParser := by
  rintro ⟨semantics, parser⟩
  have derivation : Derives anyByteFormat (Vec.singleton 0) 0 Vec.empty :=
    Derives.byte (fun _ => True) 0 Vec.empty trivial
  obtain ⟨value, rest, selected⟩ :=
    semantics.selectedComplete ⟨0, Vec.empty, derivation⟩
  have completion :
      HasSelectedCompletion semantics.selectedDerivation Vec.empty :=
    ⟨Vec.singleton 0, value, rest, by simpa using selected⟩
  have invalid := parser.invalidSound Vec.empty (.malformed "empty") rfl
  exact semantics.invalidNoCompletion invalid completion

def noByteFormat : Format Byte := .byte (fun _ => False)

def noByteSemantics : FormatSemantics noByteFormat where
  selectedDerivation _ _ _ := False
  selectionPolicy _ _ _ := True
  repairableIncompletePrefix _ _ := False
  irrecoverablyInvalidPrefix _ errorClass :=
    errorClass = .malformed
  selectedIff := by
    intro input value rest
    constructor
    · simp
    · rintro ⟨derivation, _policy⟩
      exact derivation.byteAccepted
  selectedComplete := by
    rintro input ⟨value, rest, derivation⟩
    exact False.elim derivation.byteAccepted
  selectedDeterministic := by simp
  repairableNoSelection := by simp
  repairableHasCompletion := by simp
  repairableHintExact := by simp
  repairableHintMinimal := by simp
  repairableHintUnique := by simp
  repairableComplete := by simp [HasSelectedCompletion]
  invalidNoCompletion := by simp [HasSelectedCompletion]
  invalidClassUnique := by
    rintro input first second rfl rfl
    rfl
  invalidComplete := by
    intro input _
    exact ⟨.malformed, rfl⟩

def rejectNoByte (message : String)
    (_ : Std.Logical.ByteArray) : ParseResult Byte :=
  .invalid (.malformed message)

theorem rejectNoByte_realizes (message : String) :
    ParserRealizes noByteSemantics (rejectNoByte message) := by
  constructor
  · simp [noByteSemantics]
  · simp [rejectNoByte, noByteSemantics]
  · intro input error equality
    cases equality
    rfl
  · intro input errorClass invalid
    rw [show errorClass = .malformed from invalid]
    exact ⟨.malformed message, rfl, rfl⟩
  · intro input value rest success
    simp [rejectNoByte] at success

def rejectNoByteAsUnsupported
    (_ : Std.Logical.ByteArray) : ParseResult Byte :=
  .invalid (.unsupported "wrong class")

/-- Matching diagnostic shape is insufficient when the precious class is
wrong. -/
theorem rejectNoByteAsUnsupported_not_realizable :
    ¬ParserRealizes noByteSemantics rejectNoByteAsUnsupported := by
  intro parser
  have invalid := parser.invalidSound Vec.empty
    (.unsupported "wrong class") rfl
  cases invalid

/-- Different diagnostic wording realizes the same precious error class. -/
example : ParserRealizes noByteSemantics (rejectNoByte "first wording") :=
  rejectNoByte_realizes "first wording"

/-- Replacement wording does not change the realized grammar semantics. -/
example : ParserRealizes noByteSemantics (rejectNoByte "replacement wording") :=
  rejectNoByte_realizes "replacement wording"

end Grass.Tests.Grammar
