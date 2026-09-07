import Grass.Artifact.Binary.Codec
import Grass.Artifact.Binary.Realization

/-! # Generic binary codec fixtures -/

namespace Grass.Tests.Artifact.Binary.Codec

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

def anyByteCodec : BinaryCodec Byte where
  format := anyByteFormat
  semantics := anyByteSemantics
  parse := takeByte
  write := writeByte
  parserRealizes := takeByte_realizes
  writerRealizes := writeByte_realizes
  parseWritePrefix := takeByte_writeByte_append

def byte (value : Nat) : Byte := BitVec.ofNat 8 value

example : anyByteCodec.parse
    (anyByteCodec.write (byte 7) ++ Vec.singleton (byte 8)) =
    .done (byte 7) (Vec.singleton (byte 8)) :=
  anyByteCodec.parseWritePrefix ..

example : Derives anyByteCodec.format
    (anyByteCodec.write (byte 7) ++ Vec.singleton (byte 8))
    (byte 7) (Vec.singleton (byte 8)) :=
  anyByteCodec.derives_with_suffix ..

end Grass.Tests.Artifact.Binary.Codec
