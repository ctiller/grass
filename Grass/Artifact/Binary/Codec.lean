import Grass.Grammar.Realization

/-!
# Composable binary field codecs

`BinaryCodec` is the generic junction for externally owned field vocabularies.
It retains the typed format, selected semantics, parser/writer realization
proofs, and the exact-suffix prefix law required to compose larger artifact
records. It contains no ISA, ABI, platform, or container-specific facts.
-/

namespace Grass.Artifact.Binary

open Grass.Grammar Grass.Std.Logical

/-- A parser/writer pair realizing one typed format and consuming exactly its
own written prefix in front of every suffix. -/
structure BinaryCodec (α : Type) where
  format : Format α
  semantics : FormatSemantics format
  parse : Std.Logical.ByteArray → ParseResult α
  write : α → Std.Logical.ByteArray
  parserRealizes : ParserRealizes semantics parse
  writerRealizes : WriterRealizes semantics write
  parseWritePrefix : ∀ value suffix,
    parse (write value ++ suffix) = .done value suffix

namespace BinaryCodec

/-- Run two codecs in sequence, passing the first decoded value to the codec
that selects the second field's format. -/
def seqParse {α β : Type} (left : BinaryCodec α)
    (right : α → BinaryCodec β) (input : Std.Logical.ByteArray) :
    ParseResult (α × β) :=
  match left.parse input with
  | .done first middle =>
      match (right first).parse middle with
      | .done second rest => .done (first, second) rest
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Sequential codec composition. The second codec may depend on the first
decoded value, matching `Format.seq` without importing a container schema. -/
def seq {α β : Type} (left : BinaryCodec α)
    (right : α → BinaryCodec β) : BinaryCodec (α × β) where
  format := .seq left.format (fun value => (right value).format)
  semantics := {
    selectedDerivation := fun input value rest =>
      seqParse left right input = .done value rest
    repairableIncompletePrefix := fun input hint =>
      seqParse left right input = .needMore hint
    irrecoverablyInvalidPrefix := fun input error =>
      seqParse left right input = .invalid error
    selectedSound := by
      intro input value rest parsed
      cases firstParsed : left.parse input with
      | done first middle =>
          cases secondParsed : (right first).parse middle with
          | done second tail =>
              have resultEq : ParseResult.done (first, second) tail =
                  .done value rest := by
                simpa [seqParse, firstParsed, secondParsed] using parsed
              injection resultEq with valueEq restEq
              rw [← valueEq, ← restEq]
              exact Derives.seq
                (left.parserRealizes.successSound input first middle firstParsed)
                ((right first).parserRealizes.successSound middle second tail
                  secondParsed)
          | needMore hint => simp [seqParse, firstParsed, secondParsed] at parsed
          | invalid error => simp [seqParse, firstParsed, secondParsed] at parsed
      | needMore hint => simp [seqParse, firstParsed] at parsed
      | invalid error => simp [seqParse, firstParsed] at parsed
  }
  parse := seqParse left right
  write := fun value => left.write value.1 ++ (right value.1).write value.2
  parserRealizes := by
    constructor
    · intro input value rest parsed
      cases firstParsed : left.parse input with
      | done first middle =>
          cases secondParsed : (right first).parse middle with
          | done second tail =>
              have resultEq : ParseResult.done (first, second) tail =
                  .done value rest := by
                simpa [seqParse, firstParsed, secondParsed] using parsed
              injection resultEq with valueEq restEq
              rw [← valueEq, ← restEq]
              exact Derives.seq
                (left.parserRealizes.successSound input first middle firstParsed)
                ((right first).parserRealizes.successSound middle second tail
                  secondParsed)
          | needMore hint => simp [seqParse, firstParsed, secondParsed] at parsed
          | invalid error => simp [seqParse, firstParsed, secondParsed] at parsed
      | needMore hint => simp [seqParse, firstParsed] at parsed
      | invalid error => simp [seqParse, firstParsed] at parsed
    · intro input value rest selected
      exact selected
    · intro input hint
      rfl
    · intro input error
      rfl
    · intro input value rest parsed
      exact parsed
  writerRealizes := by
    constructor
    · intro value
      exact Derives.seq
        (left.writerRealizes.derivesWithSuffix value.1
          ((right value.1).write value.2))
        ((right value.1).writerRealizes.sound value.2)
    · intro value
      have first := left.parseWritePrefix value.1
        ((right value.1).write value.2)
      have second := (right value.1).parseWritePrefix value.2 Vec.empty
      have secondExact :
          (right value.1).parse ((right value.1).write value.2) =
            .done value.2 Vec.empty := by
        simpa using second
      simp [seqParse, first, secondExact]
  parseWritePrefix := by
    intro value suffix
    have first := left.parseWritePrefix value.1
      ((right value.1).write value.2 ++ suffix)
    have second := (right value.1).parseWritePrefix value.2 suffix
    simp [seqParse, Vec.append_assoc, first, second]

/-- The empty-suffix instance agrees with the generic parser/writer theorem. -/
theorem parse_write {α : Type} (codec : BinaryCodec α) (value : α) :
    codec.parse (codec.write value) = .done value Vec.empty := by
  simpa using codec.parseWritePrefix value Vec.empty

/-- A codec writer derives its format in front of every suffix. -/
theorem derives_with_suffix {α : Type} (codec : BinaryCodec α)
    (value : α) (suffix : Std.Logical.ByteArray) :
    Derives codec.format (codec.write value ++ suffix) value suffix :=
  codec.writerRealizes.derivesWithSuffix value suffix

end BinaryCodec

end Grass.Artifact.Binary
