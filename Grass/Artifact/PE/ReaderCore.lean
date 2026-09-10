import Grass.Artifact.Binary.ReaderCore

/-! # Sequential PE reader glue -/

namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical

/-- Continue a field read with its unconsumed suffix, preserving failures. -/
abbrev continueRead {α β : Type} (result : ParseResult α)
    (next : α → Std.Logical.ByteArray → ParseResult β) : ParseResult β :=
  Binary.continueRead result next

end Grass.Artifact.PE
