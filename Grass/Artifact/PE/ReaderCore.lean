import Grass.Artifact.Binary.EndianLaws

/-! # Sequential PE reader glue -/

namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical

/-- Continue a field read with its unconsumed suffix, preserving failures. -/
def continueRead {α β : Type} (result : ParseResult α)
    (next : α → Std.Logical.ByteArray → ParseResult β) : ParseResult β :=
  match result with
  | .done value rest => next value rest
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

end Grass.Artifact.PE
