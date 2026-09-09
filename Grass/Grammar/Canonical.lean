import Grass.Grammar.Realization

/-!
# Canonical normalization of complete encodings

`normalize` accepts only complete parser successes. Its laws follow from
`parse_write`; they do not identify normalization with an independently authored
canonical policy. Prefix parsing remains available through the original parser.
-/

namespace Grass.Grammar

open Grass.Std.Logical

/-- Parse a complete value and emit its selected representation. Incomplete,
invalid, and trailing-input results have no normalization. -/
def normalize {α : Type} (parse : Std.Logical.ByteArray → ParseResult α)
    (write : α → Std.Logical.ByteArray) (input : Std.Logical.ByteArray) :
    Option Std.Logical.ByteArray :=
  match parse input with
  | .done value rest => if rest = Vec.empty then some (write value) else none
  | _ => none

/-- `normalize_of_done` identifies normalization on a complete parser success. -/
theorem normalize_of_done {α : Type}
    {parse : Std.Logical.ByteArray → ParseResult α}
    (write : α → Std.Logical.ByteArray) {input : Std.Logical.ByteArray} {value : α}
    (parsed : parse input = .done value Vec.empty) :
    normalize parse write input = some (write value) := by
  simp [normalize, parsed]

/-- `normalize_eq_some_iff` exposes the complete parsed value behind every
successful normalization; a trailing suffix cannot silently disappear. -/
theorem normalize_eq_some_iff {α : Type}
    {parse : Std.Logical.ByteArray → ParseResult α}
    {write : α → Std.Logical.ByteArray} {input output : Std.Logical.ByteArray} :
    normalize parse write input = some output ↔
      ∃ value, parse input = .done value Vec.empty ∧ write value = output := by
  cases parsed : parse input with
  | done value rest =>
      by_cases empty : rest = Vec.empty
      · subst rest
        simp [normalize, parsed]
      · simp [normalize, parsed, empty]
  | needMore hint => simp [normalize, parsed]
  | invalid error => simp [normalize, parsed]

/-- `normalize_write` fixes every emitted representation under normalization. -/
theorem normalize_write {α : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    {write : α → Std.Logical.ByteArray}
    (parser : ParserRealizes semantics parse) (writer : WriterRealizes semantics write)
    (value : α) : normalize parse write (write value) = some (write value) :=
  normalize_of_done write (parse_write parser writer value)

/-- `normalize_preserves_value` states value preservation for every completely
accepted input, including alternate encodings admitted by the selected parser. -/
theorem normalize_preserves_value {α : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    {write : α → Std.Logical.ByteArray}
    (parser : ParserRealizes semantics parse) (writer : WriterRealizes semantics write)
    {input : Std.Logical.ByteArray} {value : α}
    (parsed : parse input = .done value Vec.empty) :
    normalize parse write input = some (write value) ∧
      parse (write value) = .done value Vec.empty :=
  ⟨normalize_of_done write parsed, parse_write parser writer value⟩

/-- `normalize_idempotent` fixes every successful normalization result. -/
theorem normalize_idempotent {α : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    {write : α → Std.Logical.ByteArray}
    (parser : ParserRealizes semantics parse) (writer : WriterRealizes semantics write)
    {input output : Std.Logical.ByteArray}
    (normalized : normalize parse write input = some output) :
    normalize parse write output = some output := by
  rcases normalize_eq_some_iff.mp normalized with ⟨value, _, rfl⟩
  exact normalize_write parser writer value

end Grass.Grammar
