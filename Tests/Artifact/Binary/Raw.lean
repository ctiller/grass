import Grass.Artifact.Binary.Raw

/-! # Explicitly unverified raw artifact writer fixtures -/

namespace Grass.Tests.Artifact.Binary.Raw

open Grass.Artifact.Binary Grass.Std.Logical

structure Layout where
  name : String
  payload : Std.Logical.ByteArray
deriving Repr, DecidableEq

def writer : RawWriter Layout where
  write := Layout.payload

def layout : Layout := ⟨"fixture", Vec.fromList [0x12, 0x34]⟩

example : (writeRaw writer layout).input = layout := rfl

example : (writeRaw writer layout).bytes = Vec.fromList [0x12, 0x34] := rfl

end Grass.Tests.Artifact.Binary.Raw
