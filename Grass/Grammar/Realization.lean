import Grass.Grammar.Core

/-!
# Parser and writer realization contracts

`Format` describes derivations, but a parser also needs an explicit consumption
and disambiguation policy. `FormatSemantics` names that precious layer without
smuggling parser implementation order into choice. Optimized, generated, or
streaming parsers are interchangeable exactly when they inhabit the same
`ParserRealizes` contract.
-/

namespace Grass.Grammar

open Grass.Std.Logical

universe u

/-- Whether a selection policy chooses some result for this input. -/
def HasSelection {α : Type} (selected : Std.Logical.ByteArray → α →
    Std.Logical.ByteArray → Prop) (input : Std.Logical.ByteArray) : Prop :=
  ∃ value rest, selected input value rest

/-- Whether appending some finite suffix reaches a selected result. -/
def HasSelectedCompletion {α : Type} (selected : Std.Logical.ByteArray → α →
    Std.Logical.ByteArray → Prop) (input : Std.Logical.ByteArray) : Prop :=
  ∃ suffix value rest, selected (input ++ suffix) value rest

/-- Whether exactly `count` appended bytes reach a selected result. -/
def CompletesAfter {α : Type} (selected : Std.Logical.ByteArray → α →
    Std.Logical.ByteArray → Prop) (input : Std.Logical.ByteArray)
    (count : Nat) : Prop :=
  ∃ suffix value rest, suffix.length = count ∧
    selected (input ++ suffix) value rest

/-- Law-bearing selection and finite-prefix classification for one format.
Selection may disambiguate an unordered `Format.choice`, but it must choose one
derived result for every input on which the format derives. Repairable inputs
have no current result and do have a finite completion; invalid inputs have no
finite completion and carry only a stable `ParseErrorClass`. -/
structure FormatSemantics {α : Type} (format : Format α) where
  selectedDerivation : Std.Logical.ByteArray → α → Std.Logical.ByteArray → Prop
  selectionPolicy : Std.Logical.ByteArray → α → Std.Logical.ByteArray → Prop
  repairableIncompletePrefix : Std.Logical.ByteArray → Option Nat → Prop
  irrecoverablyInvalidPrefix : Std.Logical.ByteArray → ParseErrorClass → Prop
  selectedIff : ∀ {input value rest},
    selectedDerivation input value rest ↔
      Derives format input value rest ∧ selectionPolicy input value rest
  selectedComplete : ∀ {input},
    (∃ value rest, Derives format input value rest) →
      HasSelection selectedDerivation input
  selectedDeterministic : ∀ {input value₁ rest₁ value₂ rest₂},
    selectedDerivation input value₁ rest₁ →
    selectedDerivation input value₂ rest₂ → value₁ = value₂ ∧ rest₁ = rest₂
  repairableNoSelection : ∀ {input hint},
    repairableIncompletePrefix input hint →
      ¬HasSelection selectedDerivation input
  repairableHasCompletion : ∀ {input hint},
    repairableIncompletePrefix input hint →
      HasSelectedCompletion selectedDerivation input
  repairableHintExact : ∀ {input count},
    repairableIncompletePrefix input (some count) →
      CompletesAfter selectedDerivation input count
  repairableHintMinimal : ∀ {input count},
    repairableIncompletePrefix input (some count) →
      ∀ candidate, CompletesAfter selectedDerivation input candidate →
        count ≤ candidate
  repairableHintUnique : ∀ {input first second},
    repairableIncompletePrefix input first →
    repairableIncompletePrefix input second → first = second
  repairableComplete : ∀ {input},
    ¬HasSelection selectedDerivation input →
    HasSelectedCompletion selectedDerivation input →
      ∃ hint, repairableIncompletePrefix input hint
  invalidNoCompletion : ∀ {input errorClass},
    irrecoverablyInvalidPrefix input errorClass →
      ¬HasSelectedCompletion selectedDerivation input
  invalidClassUnique : ∀ {input first second},
    irrecoverablyInvalidPrefix input first →
    irrecoverablyInvalidPrefix input second → first = second
  invalidComplete : ∀ {input},
    ¬HasSelectedCompletion selectedDerivation input →
      ∃ errorClass, irrecoverablyInvalidPrefix input errorClass

/-- Selection is always a format derivation admitted by the explicit policy. -/
theorem FormatSemantics.selectedSound {α : Type} {format : Format α}
    (semantics : FormatSemantics format) {input value rest}
    (selected : semantics.selectedDerivation input value rest) :
    Derives format input value rest :=
  (semantics.selectedIff.1 selected).1

/-- `FormatSemantics.hasSelection_iff_derives` proves that the explicit policy
selects a result exactly on inputs recognized by the underlying format. -/
theorem FormatSemantics.hasSelection_iff_derives
    {α : Type} {format : Format α} (semantics : FormatSemantics format)
    (input : Std.Logical.ByteArray) :
    HasSelection semantics.selectedDerivation input ↔
      ∃ value rest, Derives format input value rest := by
  constructor
  · rintro ⟨value, rest, selected⟩
    exact ⟨value, rest, semantics.selectedSound selected⟩
  · exact semantics.selectedComplete

/-- `FormatSemantics.repairable_iff` characterizes repairability independently
of an executable parser; a retained hint additionally obeys the exact/minimum
laws in `FormatSemantics.repairableHintExact` and
`FormatSemantics.repairableHintMinimal`. -/
theorem FormatSemantics.repairable_iff
    {α : Type} {format : Format α} (semantics : FormatSemantics format)
    (input : Std.Logical.ByteArray) :
    (∃ hint, semantics.repairableIncompletePrefix input hint) ↔
      ¬HasSelection semantics.selectedDerivation input ∧
        HasSelectedCompletion semantics.selectedDerivation input := by
  constructor
  · rintro ⟨hint, repairable⟩
    exact ⟨semantics.repairableNoSelection repairable,
      semantics.repairableHasCompletion repairable⟩
  · rintro ⟨noSelection, completion⟩
    exact semantics.repairableComplete noSelection completion

/-- `FormatSemantics.invalid_iff` characterizes irrecoverability independently
of an executable parser as absence of every finite selected completion. -/
theorem FormatSemantics.invalid_iff
    {α : Type} {format : Format α} (semantics : FormatSemantics format)
    (input : Std.Logical.ByteArray) :
    (∃ errorClass, semantics.irrecoverablyInvalidPrefix input errorClass) ↔
      ¬HasSelectedCompletion semantics.selectedDerivation input := by
  constructor
  · rintro ⟨errorClass, invalid⟩
    exact semantics.invalidNoCompletion invalid
  · exact semantics.invalidComplete

/-- A total parser implements all four directions required by `docs/GRAMMAR.md`:
success is sound and complete for the selected derivation, and both non-success
classifications are exact biconditionals. -/
structure ParserRealizes {α : Type} {format : Format α}
    (semantics : FormatSemantics format)
    (parse : Std.Logical.ByteArray → ParseResult α) : Prop where
  successComplete : ∀ input value rest,
    semantics.selectedDerivation input value rest →
      parse input = .done value rest
  needMoreExact : ∀ input hint,
    parse input = .needMore hint ↔
      semantics.repairableIncompletePrefix input hint
  invalidSound : ∀ input error,
    parse input = .invalid error →
      semantics.irrecoverablyInvalidPrefix input error.class
  invalidComplete : ∀ input errorClass,
    semantics.irrecoverablyInvalidPrefix input errorClass →
      ∃ error, error.class = errorClass ∧ parse input = .invalid error
  consumes : ∀ input value rest,
    parse input = .done value rest →
      semantics.selectedDerivation input value rest

/-- Successful parsing is sound because a realized parser selects a semantic
derivation and the selected semantics is itself sound for the format. -/
theorem ParserRealizes.successSound {α : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    (parser : ParserRealizes semantics parse) (input : Std.Logical.ByteArray)
    (value : α) (rest : Std.Logical.ByteArray)
    (parsed : parse input = .done value rest) :
    Derives format input value rest :=
  semantics.selectedSound (parser.consumes input value rest parsed)

/-- `ParserRealizes.invalid_iff_exists_classified_error` gives exact invalid
classification modulo non-precious diagnostic wording. -/
theorem ParserRealizes.invalid_iff_exists_classified_error
    {α : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    (parser : ParserRealizes semantics parse) (input : Std.Logical.ByteArray)
    (errorClass : ParseErrorClass) :
    (∃ error, error.class = errorClass ∧ parse input = .invalid error) ↔
      semantics.irrecoverablyInvalidPrefix input errorClass := by
  constructor
  · rintro ⟨error, rfl, parsed⟩
    exact parser.invalidSound input error parsed
  · exact parser.invalidComplete input errorClass

/-- `ParserRealizes.consumesPrefix` proves that a successful realized parser
returns the exact suffix after some consumed prefix. -/
theorem ParserRealizes.consumesPrefix {α : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    (parser : ParserRealizes semantics parse) (input : Std.Logical.ByteArray)
    (value : α) (rest : Std.Logical.ByteArray)
    (parsed : parse input = .done value rest) :
    ∃ consumed, input = consumed ++ rest :=
  (parser.successSound input value rest parsed).consumesPrefix

/-- A canonical writer emits a valid selected derivation. Requiring selection,
not only derivability, is what lets parser completeness prove the public
round-trip theorem even for an ambiguous underlying grammar. -/
structure WriterRealizes {α : Type} {format : Format α}
    (semantics : FormatSemantics format)
    (write : α → Std.Logical.ByteArray) : Prop where
  sound : ∀ value, Derives format (write value) value Vec.empty
  selected : ∀ value,
    semantics.selectedDerivation (write value) value Vec.empty

/-- A realized writer's derivation is valid in front of every suffix. This is
the compositional form of writer soundness; it follows from the format law and
does not ask the writer implementation for a second proof. -/
theorem WriterRealizes.derivesWithSuffix {α : Type} {format : Format α}
    {semantics : FormatSemantics format} {write : α → Std.Logical.ByteArray}
    (writer : WriterRealizes semantics write) (value : α)
    (suffix : Std.Logical.ByteArray) :
    Derives format (write value ++ suffix) value suffix := by
  simpa using (writer.sound value).appendSuffix suffix

/-- Parser and writer realizations of the same selected language round-trip at
the modeled value level and consume the complete written input. -/
theorem parse_write {α : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    {write : α → Std.Logical.ByteArray}
    (parser : ParserRealizes semantics parse)
    (writer : WriterRealizes semantics write) (value : α) :
    parse (write value) = .done value Vec.empty :=
  parser.successComplete (write value) value Vec.empty (writer.selected value)

/-! ## Realization transport across format isomorphisms -/

/-- Transport selected semantics across a total value isomorphism. Prefix
classification is unchanged because the byte language is unchanged. -/
def FormatSemantics.iso {α β : Type} {format : Format α}
    (semantics : FormatSemantics format) (isomorphism : Isomorphism α β) :
    FormatSemantics (.iso format isomorphism) where
  selectedDerivation input value rest :=
    semantics.selectedDerivation input (isomorphism.backward value) rest
  selectionPolicy input value rest :=
    semantics.selectionPolicy input (isomorphism.backward value) rest
  repairableIncompletePrefix := semantics.repairableIncompletePrefix
  irrecoverablyInvalidPrefix := semantics.irrecoverablyInvalidPrefix
  selectedIff := by
    intro input value rest
    constructor
    · intro selected
      rcases semantics.selectedIff.1 selected with ⟨derived, policy⟩
      constructor
      · have mapped := @Derives.iso α β format isomorphism input rest
          (isomorphism.backward value) derived
        simpa only [isomorphism.forward_backward] using mapped
      · exact policy
    · rintro ⟨derived, policy⟩
      exact semantics.selectedIff.2 ⟨derived.iso_inner, policy⟩
  selectedComplete := by
    rintro input ⟨value, rest, derived⟩
    rcases semantics.selectedComplete
        ⟨isomorphism.backward value, rest, derived.iso_inner⟩ with
      ⟨innerValue, innerRest, selected⟩
    exact ⟨isomorphism.forward innerValue, innerRest, by
      simpa only [isomorphism.backward_forward] using selected⟩
  selectedDeterministic := by
    intro input value₁ rest₁ value₂ rest₂ first second
    have unique := semantics.selectedDeterministic first second
    constructor
    · calc
        value₁ = isomorphism.forward (isomorphism.backward value₁) :=
          (isomorphism.forward_backward value₁).symm
        _ = isomorphism.forward (isomorphism.backward value₂) :=
          congrArg isomorphism.forward unique.1
        _ = value₂ := isomorphism.forward_backward value₂
    · exact unique.2
  repairableNoSelection := by
    intro input hint repairable selected
    apply semantics.repairableNoSelection repairable
    rcases selected with ⟨value, rest, chosen⟩
    exact ⟨isomorphism.backward value, rest, chosen⟩
  repairableHasCompletion := by
    intro input hint repairable
    rcases semantics.repairableHasCompletion repairable with
      ⟨suffix, value, rest, selected⟩
    exact ⟨suffix, isomorphism.forward value, rest, by
      simpa only [isomorphism.backward_forward] using selected⟩
  repairableHintExact := by
    intro input count repairable
    rcases semantics.repairableHintExact repairable with
      ⟨suffix, value, rest, suffixLength, selected⟩
    exact ⟨suffix, isomorphism.forward value, rest, suffixLength, by
      simpa only [isomorphism.backward_forward] using selected⟩
  repairableHintMinimal := by
    intro input count repairable candidate completion
    apply semantics.repairableHintMinimal repairable candidate
    rcases completion with ⟨suffix, value, rest, suffixLength, selected⟩
    exact ⟨suffix, isomorphism.backward value, rest, suffixLength, selected⟩
  repairableHintUnique := semantics.repairableHintUnique
  repairableComplete := by
    intro input noSelection completion
    apply semantics.repairableComplete
    · intro innerSelection
      apply noSelection
      rcases innerSelection with ⟨value, rest, selected⟩
      exact ⟨isomorphism.forward value, rest, by
        simpa only [isomorphism.backward_forward] using selected⟩
    · rcases completion with ⟨suffix, value, rest, selected⟩
      exact ⟨suffix, isomorphism.backward value, rest, selected⟩
  invalidNoCompletion := by
    intro input errorClass invalid completion
    apply semantics.invalidNoCompletion invalid
    rcases completion with ⟨suffix, value, rest, selected⟩
    exact ⟨suffix, isomorphism.backward value, rest, selected⟩
  invalidClassUnique := semantics.invalidClassUnique
  invalidComplete := by
    intro input noCompletion
    apply semantics.invalidComplete
    intro innerCompletion
    apply noCompletion
    rcases innerCompletion with ⟨suffix, value, rest, selected⟩
    exact ⟨suffix, isomorphism.forward value, rest, by
      simpa only [isomorphism.backward_forward] using selected⟩

/-- Map only successful parse values, preserving both failure classifications
and the exact unconsumed suffix. -/
def ParseResult.map {α β : Type} (forward : α → β) : ParseResult α → ParseResult β
  | .done value rest => .done (forward value) rest
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Lift an executable parser through a total value isomorphism. -/
def isoParser {α β : Type} (isomorphism : Isomorphism α β)
    (parse : Std.Logical.ByteArray → ParseResult α) :
    Std.Logical.ByteArray → ParseResult β :=
  fun input => (parse input).map isomorphism.forward

/-- Lift an executable writer contravariantly through a total value
isomorphism. -/
def isoWriter {α β : Type} (isomorphism : Isomorphism α β)
    (write : α → Std.Logical.ByteArray) : β → Std.Logical.ByteArray :=
  fun value => write (isomorphism.backward value)

/-- `ParserRealizes.iso` states that parser realization is preserved by total
value isomorphisms. -/
theorem ParserRealizes.iso {α β : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    (parser : ParserRealizes semantics parse)
    (isomorphism : Isomorphism α β) :
    ParserRealizes (semantics.iso isomorphism) (isoParser isomorphism parse) := by
  constructor
  · intro input value rest selected
    unfold isoParser
    rw [parser.successComplete input (isomorphism.backward value) rest selected]
    simp [ParseResult.map, isomorphism.forward_backward]
  · intro input hint
    unfold isoParser FormatSemantics.iso
    cases parsed : parse input with
    | done value rest =>
        have notNeedMore :
            ¬semantics.repairableIncompletePrefix input hint := by
          intro repairable
          have := parser.needMoreExact input hint |>.2 repairable
          rw [parsed] at this
          contradiction
        simp [ParseResult.map, notNeedMore]
    | needMore actualHint =>
        simp only [ParseResult.map, ParseResult.needMore.injEq]
        constructor
        · intro equal
          subst hint
          exact parser.needMoreExact input actualHint |>.1 parsed
        · intro repairable
          have exactResult := parser.needMoreExact input hint |>.2 repairable
          exact ParseResult.needMore.inj (parsed.symm.trans exactResult)
    | invalid error =>
        have notNeedMore :
            ¬semantics.repairableIncompletePrefix input hint := by
          intro repairable
          have := parser.needMoreExact input hint |>.2 repairable
          rw [parsed] at this
          contradiction
        simp [ParseResult.map, notNeedMore]
  · intro input error
    unfold isoParser
    cases parsed : parse input with
    | done value rest =>
        simp [ParseResult.map]
    | needMore hint =>
        simp [ParseResult.map]
    | invalid actualError =>
        simp only [ParseResult.map, ParseResult.invalid.injEq]
        intro equal
        subst error
        unfold FormatSemantics.iso
        exact parser.invalidSound input actualError parsed
  · intro input errorClass invalid
    rcases parser.invalidComplete input errorClass invalid with
      ⟨error, classEq, parsed⟩
    exact ⟨error, classEq, by
      unfold isoParser
      rw [parsed]
      rfl⟩
  · intro input value rest success
    unfold isoParser at success
    cases parsed : parse input with
    | done innerValue innerRest =>
        rw [parsed] at success
        simp only [ParseResult.map] at success
        injection success with valueEq restEq
        subst value
        subst rest
        have selected := parser.consumes input innerValue innerRest parsed
        unfold FormatSemantics.iso
        simpa only [isomorphism.backward_forward] using selected
    | needMore hint =>
        rw [parsed] at success
        simp [ParseResult.map] at success
    | invalid error =>
        rw [parsed] at success
        simp [ParseResult.map] at success

/-- `WriterRealizes.iso` states that writer realization is preserved by total
value isomorphisms. -/
theorem WriterRealizes.iso {α β : Type} {format : Format α}
    {semantics : FormatSemantics format} {write : α → Std.Logical.ByteArray}
    (writer : WriterRealizes semantics write)
    (isomorphism : Isomorphism α β) :
    WriterRealizes (semantics.iso isomorphism) (isoWriter isomorphism write) := by
  constructor
  · intro value
    unfold isoWriter
    have derivation : Derives (.iso format isomorphism)
        (write (isomorphism.backward value))
        (isomorphism.forward (isomorphism.backward value)) Vec.empty :=
      @Derives.iso α β format isomorphism (write (isomorphism.backward value))
        Vec.empty (isomorphism.backward value)
        (writer.sound (isomorphism.backward value))
    rw [isomorphism.forward_backward] at derivation
    exact derivation
  · intro value
    unfold isoWriter FormatSemantics.iso
    exact writer.selected (isomorphism.backward value)

/-! ## The generic one-byte language -/

/-- Every byte is accepted. Instruction-specific byte predicates do not belong
here; their owning ISA may build a refined format above this one. -/
def anyByteFormat : Format Byte := .byte (fun _ => True)

/-- `derives_anyByteFormat_iff` characterizes the generic byte language without
reference to any executable parser. -/
theorem derives_anyByteFormat_iff (input : Std.Logical.ByteArray)
    (value : Byte) (rest : Std.Logical.ByteArray) :
    Derives anyByteFormat input value rest ↔
      input = Vec.singleton value ++ rest := by
  constructor
  · exact fun derivation => derivation.byteInput
  · intro equality
    rw [equality]
    exact Derives.byte (fun _ => True) value rest trivial

/-- A one-byte prefix is the sole selected derivation. Empty input is repairable
by exactly one byte, and no finite prefix is irrecoverably invalid. -/
def anyByteSemantics : FormatSemantics anyByteFormat where
  selectedDerivation input value rest := input = Vec.singleton value ++ rest
  selectionPolicy _ _ _ := True
  repairableIncompletePrefix input hint := input = Vec.empty ∧ hint = some 1
  irrecoverablyInvalidPrefix _ _ := False
  selectedIff := by
    intro input value rest
    rw [derives_anyByteFormat_iff]
    simp
  selectedComplete := by
    rintro input ⟨value, rest, derivation⟩
    exact ⟨value, rest,
      (derives_anyByteFormat_iff input value rest).1 derivation⟩
  selectedDeterministic := by
    intro input value₁ rest₁ value₂ rest₂ first second
    rw [first] at second
    have listEquality := congrArg Vec.toList second
    have parts : value₁ = value₂ ∧ rest₁.toList = rest₂.toList := by
      simpa [Vec.singleton] using listEquality
    exact ⟨parts.1, Vec.toList_injective parts.2⟩
  repairableNoSelection := by
    rintro input hint ⟨rfl, rfl⟩ ⟨value, rest, selected⟩
    have lengthEquality := congrArg Vec.length selected
    simp at lengthEquality
    omega
  repairableHasCompletion := by
    rintro input hint ⟨rfl, rfl⟩
    exact ⟨Vec.singleton 0, 0, Vec.empty, by simp⟩
  repairableHintExact := by
    rintro input count ⟨rfl, equality⟩
    cases equality
    exact ⟨Vec.singleton 0, 0, Vec.empty, by simp⟩
  repairableHintMinimal := by
    rintro input count ⟨rfl, equality⟩ candidate
      ⟨suffix, value, rest, suffixLength, selected⟩
    cases equality
    have inputLength := congrArg Vec.length selected
    simp [Vec.length_append, suffixLength] at inputLength
    omega
  repairableHintUnique := by
    rintro input first second ⟨_, rfl⟩ ⟨_, rfl⟩
    rfl
  repairableComplete := by
    intro input noSelection _completion
    cases input with
    | fromList bytes =>
      cases bytes with
      | nil => exact ⟨some 1, rfl, rfl⟩
      | cons value rest =>
        exfalso
        apply noSelection
        exact ⟨value, Vec.fromList rest, rfl⟩
  invalidNoCompletion := by simp
  invalidClassUnique := by simp
  invalidComplete := by
    intro input noCompletion
    exfalso
    apply noCompletion
    cases input with
    | fromList bytes =>
      cases bytes with
      | nil => exact ⟨Vec.singleton 0, 0, Vec.empty, by rfl⟩
      | cons value rest =>
        refine ⟨Vec.empty, value, Vec.fromList rest, ?_⟩
        rw [Vec.append_empty]
        rfl

/-- `FormatSemantics.classifies` proves that every input inhabits a selected,
repairable, or irrecoverable outcome family. -/
theorem FormatSemantics.classifies {α : Type} {format : Format α}
    (semantics : FormatSemantics format) (input : Std.Logical.ByteArray) :
    HasSelection semantics.selectedDerivation input ∨
      (∃ hint, semantics.repairableIncompletePrefix input hint) ∨
      (∃ errorClass, semantics.irrecoverablyInvalidPrefix input errorClass) := by
  classical
  by_cases selected : HasSelection semantics.selectedDerivation input
  · exact Or.inl selected
  · by_cases completion :
        HasSelectedCompletion semantics.selectedDerivation input
    · exact Or.inr (Or.inl (semantics.repairableComplete selected completion))
    · exact Or.inr (Or.inr (semantics.invalidComplete completion))

/-- A selected result and a repairable classification are disjoint. -/
theorem FormatSemantics.selection_not_repairable
    {α : Type} {format : Format α} (semantics : FormatSemantics format)
    {input : Std.Logical.ByteArray} {hint : Option Nat}
    (selected : HasSelection semantics.selectedDerivation input) :
    ¬semantics.repairableIncompletePrefix input hint := by
  intro repairable
  exact semantics.repairableNoSelection repairable selected

/-- A selected result and an irrecoverable classification are disjoint. -/
theorem FormatSemantics.selection_not_invalid
    {α : Type} {format : Format α} (semantics : FormatSemantics format)
    {input : Std.Logical.ByteArray} {errorClass : ParseErrorClass}
    (selected : HasSelection semantics.selectedDerivation input) :
    ¬semantics.irrecoverablyInvalidPrefix input errorClass := by
  intro invalid
  apply semantics.invalidNoCompletion invalid
  rcases selected with ⟨value, rest, selected⟩
  exact ⟨Vec.empty, value, rest, by simpa using selected⟩

/-- Repairable and irrecoverable classifications are disjoint. -/
theorem FormatSemantics.repairable_not_invalid
    {α : Type} {format : Format α} (semantics : FormatSemantics format)
    {input : Std.Logical.ByteArray} {hint : Option Nat}
    {errorClass : ParseErrorClass}
    (repairable : semantics.repairableIncompletePrefix input hint) :
    ¬semantics.irrecoverablyInvalidPrefix input errorClass := by
  intro invalid
  exact semantics.invalidNoCompletion invalid
    (semantics.repairableHasCompletion repairable)

end Grass.Grammar
