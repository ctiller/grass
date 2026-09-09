import Grass.Grammar.Core

namespace Grass

/-- Artifact construction and parsing share an exact decoded view. The parsed
view may differ from the proof-bearing construction plan, as it does for PE.
This is a syntax/byte contract and supplies no loaded execution semantics. -/
structure ArtifactEncoding where
  Artifact : Type
  Parsed : Type
  write : Artifact → Std.Logical.ByteArray
  read : Std.Logical.ByteArray → Grammar.ParseResult Parsed
  decoded : Artifact → Parsed
  read_write : ∀ artifact, read (write artifact) = .done (decoded artifact) Std.Logical.Vec.empty

end Grass
