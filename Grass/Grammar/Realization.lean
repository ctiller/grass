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
  successSound : ∀ input value rest,
    parse input = .done value rest → Derives format input value rest
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

/-- A canonical writer emits a valid selected derivation. Requiring selection,
not only derivability, is what lets parser completeness prove the public
round-trip theorem even for an ambiguous underlying grammar. -/
structure WriterRealizes {α : Type} {format : Format α}
    (semantics : FormatSemantics format)
    (write : α → Std.Logical.ByteArray) : Prop where
  sound : ∀ value, Derives format (write value) value Vec.empty
  selected : ∀ value,
    semantics.selectedDerivation (write value) value Vec.empty

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

/-- The primitive executable parser realizes the generic one-byte language. -/
theorem takeByte_realizes : ParserRealizes anyByteSemantics takeByte := by
  constructor
  · intro input value rest success
    exact anyByteSemantics.selectedSound (takeByte_done success)
  · intro input value rest selected
    exact takeByte_writeByte_append value rest ▸ congrArg takeByte selected
  · intro input hint
    cases input with
    | fromList bytes =>
      cases bytes with
      | nil => simp [takeByte, anyByteSemantics, Vec.empty, Vec.get?, eq_comm]
      | cons first tail =>
        simp [takeByte, anyByteSemantics, Vec.empty, Vec.get?]
  · intro input error
    cases input with
    | fromList bytes =>
      cases bytes with
      | nil => simp [takeByte, anyByteSemantics, Vec.get?]
      | cons first tail =>
        simp [takeByte, anyByteSemantics, Vec.get?]
  · intro input value rest success
    exact takeByte_done success

/-- The one-byte writer realizes the same selected language. -/
theorem writeByte_realizes : WriterRealizes anyByteSemantics writeByte := by
  constructor
  · intro value
    exact Derives.byte (fun _ => True) value Vec.empty trivial
  · intro value
    simp [anyByteSemantics, writeByte]

/-- The generic realization theorem specializes to the executable byte
round-trip rather than relying on reduction of the implementation. -/
theorem takeByte_writeByte_via_realization (value : Byte) :
    takeByte (writeByte value) = .done value Vec.empty :=
  parse_write takeByte_realizes writeByte_realizes value

end Grass.Grammar
