import Grass.Artifact.Binary.Realization
import Grass.Grammar.Streaming

/-! # Chunk-invariant streaming parser fixtures -/

namespace Grass.Tests.Grammar.Streaming

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

def byte (value : Nat) : Byte := BitVec.ofNat 8 value

def splitChunks : Vec Std.Logical.ByteArray :=
  Vec.singleton (Vec.singleton (byte 7)) ++
    Vec.singleton (Vec.singleton (byte 8))

def joinedChunk : Vec Std.Logical.ByteArray :=
  Vec.singleton (Vec.singleton (byte 7) ++ Vec.singleton (byte 8))

example : Vec.flatten splitChunks = Vec.flatten joinedChunk := by
  simp [splitChunks, joinedChunk]

example :
    (StreamingParser.buffered takeByte).finish
        ((StreamingParser.buffered takeByte).feedAll splitChunks) =
      .done (byte 7) (Vec.singleton (byte 8)) := by
  have chunking : Vec.IsChunking splitChunks
      (writeByte (byte 7) ++ Vec.singleton (byte 8)) := by
    simp [Vec.IsChunking, splitChunks, writeByte]
  rw [(StreamingParser.buffered takeByte).finish_of_isChunking chunking]
  exact takeByte_writeByte_append (byte 7) (Vec.singleton (byte 8))

example :
    (StreamingParser.buffered takeByte).finish
        ((StreamingParser.buffered takeByte).feedAll splitChunks) =
      (StreamingParser.buffered takeByte).finish
        ((StreamingParser.buffered takeByte).feedAll joinedChunk) := by
  apply StreamingParser.finish_eq_of_flatten_eq
  simp [splitChunks, joinedChunk]

example : StreamingRealizes anyByteSemantics takeByte :=
  takeByte_realizes.bufferedStreaming

end Grass.Tests.Grammar.Streaming
