import Grass.Artifact.Binary.EndianLaws

/-! # Shared sequential binary reader glue -/

namespace Grass.Artifact.Binary

open Grass.Grammar

/-- Continue with the exact unconsumed suffix, preserving both failure classes. -/
def continueRead {α β : Type} (result : ParseResult α)
    (next : α → Std.Logical.ByteArray → ParseResult β) : ParseResult β :=
  match result with
  | .done value rest => next value rest
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

end Grass.Artifact.Binary
