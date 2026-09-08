import Grass.Artifact.Binary.Realization
import Grass.Grammar.Endian

/-!
# Concrete endian readers and writers

These implementations transport the exact-width byte reader and writer through
the total endian isomorphisms. They contain no instruction-set encoding facts.
-/

namespace Grass.Artifact.Binary

open Grass.Std.Logical Grass.Grammar

/-- Parse an exact-width big-endian integer while preserving the input suffix. -/
def takeBigEndian (count : Nat) :
    Std.Logical.ByteArray → ParseResult (BitVec (8 * count)) :=
  isoParser (bigEndianIsomorphism count) (takeExactSized count)

/-- Write a fixed-width integer in most-significant-byte-first order. -/
def writeBigEndian {count : Nat} : BitVec (8 * count) → Std.Logical.ByteArray :=
  isoWriter (bigEndianIsomorphism count) (@writeExact count)

/-- A fixed-width big-endian writer emits exactly its type-level byte count. -/
@[simp] theorem length_writeBigEndian {count : Nat}
    (value : BitVec (8 * count)) : (writeBigEndian value).length = count := by
  unfold writeBigEndian isoWriter writeExact
  exact (bigEndianIsomorphism count).backward value |>.2

/-- The concrete big-endian reader realizes the transported selected semantics. -/
theorem takeBigEndian_realizes (count : Nat) :
    ParserRealizes (bigEndianSemantics count) (takeBigEndian count) :=
  (takeExactSized_realizes count).iso (bigEndianIsomorphism count)

/-- The concrete big-endian writer realizes the transported selected semantics. -/
theorem writeBigEndian_realizes (count : Nat) :
    WriterRealizes (bigEndianSemantics count) (@writeBigEndian count) :=
  (writeExact_realizes count).iso (bigEndianIsomorphism count)

/-- `takeBigEndian_writeBigEndian` states the complete-input big-endian
reader/writer round trip. -/
@[simp] theorem takeBigEndian_writeBigEndian {count : Nat}
    (value : BitVec (8 * count)) :
    takeBigEndian count (writeBigEndian value) = .done value Vec.empty :=
  parse_write (takeBigEndian_realizes count) (writeBigEndian_realizes count) value

/-- Parse an exact-width little-endian integer while preserving the input suffix. -/
def takeLittleEndian (count : Nat) :
    Std.Logical.ByteArray → ParseResult (BitVec (8 * count)) :=
  isoParser (littleEndianIsomorphism count) (takeExactSized count)

/-- Write a fixed-width integer in least-significant-byte-first order. -/
def writeLittleEndian {count : Nat} : BitVec (8 * count) → Std.Logical.ByteArray :=
  isoWriter (littleEndianIsomorphism count) (@writeExact count)

/-- A fixed-width little-endian writer emits exactly its type-level byte count. -/
@[simp] theorem length_writeLittleEndian {count : Nat}
    (value : BitVec (8 * count)) : (writeLittleEndian value).length = count := by
  unfold writeLittleEndian isoWriter writeExact
  exact (littleEndianIsomorphism count).backward value |>.2

/-- A little-endian value written before any suffix is consumed exactly,
leaving that suffix unchanged. -/
@[simp] theorem takeLittleEndian_writeLittleEndian_append {count : Nat}
    (value : BitVec (8 * count)) (rest : Std.Logical.ByteArray) :
    takeLittleEndian count (writeLittleEndian value ++ rest) = .done value rest := by
  unfold takeLittleEndian writeLittleEndian isoParser isoWriter
  rw [takeExactSized_writeExact_append]
  simp only [ParseResult.map, ParseResult.done.injEq, and_true]
  exact (littleEndianIsomorphism count).forward_backward value

/-- The concrete little-endian reader realizes the transported selected semantics. -/
theorem takeLittleEndian_realizes (count : Nat) :
    ParserRealizes (littleEndianSemantics count) (takeLittleEndian count) :=
  (takeExactSized_realizes count).iso (littleEndianIsomorphism count)

/-- The concrete little-endian writer realizes the transported selected semantics. -/
theorem writeLittleEndian_realizes (count : Nat) :
    WriterRealizes (littleEndianSemantics count) (@writeLittleEndian count) :=
  (writeExact_realizes count).iso (littleEndianIsomorphism count)

/-- `takeLittleEndian_writeLittleEndian` states the complete-input little-endian
reader/writer round trip. -/
@[simp] theorem takeLittleEndian_writeLittleEndian {count : Nat}
    (value : BitVec (8 * count)) :
    takeLittleEndian count (writeLittleEndian value) = .done value Vec.empty :=
  parse_write (takeLittleEndian_realizes count) (writeLittleEndian_realizes count) value

end Grass.Artifact.Binary
