import Grass.Artifact.PE.ReaderCore
import Grass.Artifact.PE.HeaderPrefix

/-! # DOS-aware PE header field reader -/

namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical Grass.Artifact.Binary

/-- Complete DOS, signature and COFF prefix fields, including reserved bytes. -/
structure ParsedHeaderPrefix where
  dosMagic : Std.Logical.ByteArray
  dosCompatibility : Std.Logical.ByteArray
  ntOffset : BitVec 32
  signature : Std.Logical.ByteArray
  machine : BitVec 16
  sectionCount : BitVec 16
  timestamp : BitVec 32
  symbolTablePointer : BitVec 32
  numberOfSymbols : BitVec 32
  optionalHeaderSize : BitVec 16
  characteristics : BitVec 16
deriving DecidableEq, Repr

/-- Decode the 88-byte prefix without consulting the writer. -/
def readHeaderPrefix (input : Std.Logical.ByteArray) : ParseResult ParsedHeaderPrefix :=
  continueRead (takeExact 2 input) fun dosMagic input =>
  continueRead (takeExact 58 input) fun dosCompatibility input =>
  continueRead (takeLittleEndian 4 input) fun ntOffset input =>
  continueRead (takeExact 4 input) fun signature input =>
  continueRead (takeLittleEndian 2 input) fun machine input =>
  continueRead (takeLittleEndian 2 input) fun sectionCount input =>
  continueRead (takeLittleEndian 4 input) fun timestamp input =>
  continueRead (takeLittleEndian 4 input) fun symbolTablePointer input =>
  continueRead (takeLittleEndian 4 input) fun numberOfSymbols input =>
  continueRead (takeLittleEndian 2 input) fun optionalHeaderSize input =>
  continueRead (takeLittleEndian 2 input) fun characteristics input =>
  .done { dosMagic, dosCompatibility, ntOffset, signature, machine, sectionCount, timestamp, symbolTablePointer, numberOfSymbols, optionalHeaderSize, characteristics } input

/-- Expected prefix field values for a serialized section count. -/
def expectedHeaderPrefix (sectionCount : BitVec 16) : ParsedHeaderPrefix where
  dosMagic := Vec.fromList [0x4d, 0x5a]
  dosCompatibility := Vec.replicate 58 0
  ntOffset := BitVec.ofNat 32 canonicalPeOffset
  signature := Vec.fromList [0x50, 0x45, 0, 0]
  machine := amd64Machine
  sectionCount := sectionCount
  timestamp := 0
  symbolTablePointer := 0
  numberOfSymbols := 0
  optionalHeaderSize := 240
  characteristics := executableImageCharacteristics

/-- `readHeaderPrefix_write_append` proves full field recovery with an arbitrary suffix. -/
theorem readHeaderPrefix_write_append (sectionCount : BitVec 16)
    (suffix : Std.Logical.ByteArray) :
    readHeaderPrefix (writeHeaderPrefix sectionCount ++ suffix) =
      .done (expectedHeaderPrefix sectionCount) suffix := by
  simp only [readHeaderPrefix, writeHeaderPrefix, writeHeaderPrefixLeading,
    writeHeaderPrefixTrailing, writeCanonicalDosHeader, writePeSignature,
    Vec.append_assoc]
  rw [takeExact_append (by simp : (Vec.fromList [0x4d, 0x5a] : Std.Logical.ByteArray).length = 2)]
  simp only [continueRead]
  rw [takeExact_append (by simp : (Vec.replicate 58 (0 : Byte)).length = 58)]
  simp only [takeLittleEndian_writeLittleEndian_append]
  rw [takeExact_append (by simp : (Vec.fromList [0x50, 0x45, 0, 0] : Std.Logical.ByteArray).length = 4)]
  simp only [takeLittleEndian_writeLittleEndian_append]
  rfl

end Grass.Artifact.PE
