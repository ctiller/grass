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

/-- The selected derivations and exact finite-prefix classification for one
format. Selection is separate from the unordered union denoted by
`Format.choice`. -/
structure FormatSemantics {α : Type} (format : Format α) where
  selectedDerivation : Std.Logical.ByteArray → α → Std.Logical.ByteArray → Prop
  repairableIncompletePrefix : Std.Logical.ByteArray → Option Nat → Prop
  irrecoverablyInvalidPrefix : Std.Logical.ByteArray → ParseError → Prop
  selectedSound : ∀ {input value rest},
    selectedDerivation input value rest → Derives format input value rest

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
  invalidExact : ∀ input error,
    parse input = .invalid error ↔
      semantics.irrecoverablyInvalidPrefix input error
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
  repairableIncompletePrefix := semantics.repairableIncompletePrefix
  irrecoverablyInvalidPrefix := semantics.irrecoverablyInvalidPrefix
  selectedSound := by
    intro input value rest selected
    have derivation : Derives (.iso format isomorphism) input
        (isomorphism.forward (isomorphism.backward value)) rest :=
      @Derives.iso α β format isomorphism input rest
        (isomorphism.backward value) (semantics.selectedSound selected)
    rw [isomorphism.forward_backward] at derivation
    exact derivation

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
    unfold isoParser FormatSemantics.iso
    cases parsed : parse input with
    | done value rest =>
        have notInvalid :
            ¬semantics.irrecoverablyInvalidPrefix input error := by
          intro invalid
          have := parser.invalidExact input error |>.2 invalid
          rw [parsed] at this
          contradiction
        simp [ParseResult.map, notInvalid]
    | needMore hint =>
        have notInvalid :
            ¬semantics.irrecoverablyInvalidPrefix input error := by
          intro invalid
          have := parser.invalidExact input error |>.2 invalid
          rw [parsed] at this
          contradiction
        simp [ParseResult.map, notInvalid]
    | invalid actualError =>
        simp only [ParseResult.map, ParseResult.invalid.injEq]
        constructor
        · intro equal
          subst error
          exact parser.invalidExact input actualError |>.1 parsed
        · intro invalid
          have exactResult := parser.invalidExact input error |>.2 invalid
          exact ParseResult.invalid.inj (parsed.symm.trans exactResult)
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

/-- A one-byte prefix is the sole selected derivation. Empty input is repairable
by exactly one byte, and no finite prefix is irrecoverably invalid. -/
def anyByteSemantics : FormatSemantics anyByteFormat where
  selectedDerivation input value rest := input = Vec.singleton value ++ rest
  repairableIncompletePrefix input hint := input = Vec.empty ∧ hint = some 1
  irrecoverablyInvalidPrefix _ _ := False
  selectedSound := by
    intro input value rest selected
    rw [selected]
    exact Derives.byte (fun _ => True) value rest trivial

end Grass.Grammar
