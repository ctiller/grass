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
