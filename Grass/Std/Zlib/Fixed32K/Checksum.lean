import Grass.Std.Zlib.CRC32
import Grass.Std.Zlib.Gzip.Trailer

/-!
# Fixed32K input accounting and trailer connection

This is the checksum/count portion of the implementation model demanded by
`Spikes/3_Gzip/Assembly.lean`: raw CRC starts at all ones, each consumed byte
uses eight branchless reflected steps, the 32-bit input count wraps, and the
trailer complements the CRC. `account_represents` connects arbitrary read
fragments to the input-prefix checksum. This module does not certify the x86
instructions, DEFLATE construction, provider effects, or allocation behavior.
-/

namespace Grass.Std.Zlib.Fixed32K

open Grass.Std.Logical

/-- Bounded arithmetic state for the authored `crc` and `totalInput` fields.
The logical input prefix is an argument of `Represents`, not retained state. -/
structure ChecksumState where
  rawCrc : BitVec 32
  inputSize : BitVec 32
deriving DecidableEq, Repr

namespace ChecksumState

/-- Initial values before any input is consumed. -/
def initial : ChecksumState := ⟨CRC32.initial, 0⟩

/-- Account for exactly the bytes returned by one successful read. Input
fragmentation is unrestricted; the surrounding model owns the 32KiB buffer. -/
def account (state : ChecksumState) (bytes : Logical.ByteArray) : ChecksumState :=
  ⟨CRC32.maskedUpdateRaw CRC32.polynomial state.rawCrc bytes,
    state.inputSize + BitVec.ofNat 32 bytes.length⟩

/-- `account_append` proves chunk independence for every starting state,
including the machine counter's wrapping arithmetic. -/
theorem account_append (state : ChecksumState) (left right : Logical.ByteArray) :
    account state (left ++ right) = account (account state left) right := by
  simp [account, ← CRC32.updateRaw_eq_maskedUpdateRaw, CRC32.updateRaw_append,
    BitVec.ofNat_add, BitVec.add_assoc]

/-- Relate both live arithmetic fields to the exact input prefix at a completed
checksum-update frontier. The authored code increments the size before its
per-byte CRC loop, so this is not an invariant of every intermediate instruction. -/
def Represents (state : ChecksumState) (input : Logical.ByteArray) : Prop :=
  state.rawCrc = CRC32.updateRaw CRC32.polynomial CRC32.initial input ∧
    state.inputSize = BitVec.ofNat 32 input.length

/-- `initial_represents` establishes the empty consumed prefix. -/
theorem initial_represents : Represents initial Vec.empty := by
  simp [Represents, initial, CRC32.updateRaw]

/-- `account_represents` connects the branchless consumer to the checksum of
the exact concatenated prefix, including modulo-2^32 input-length accounting. -/
theorem account_represents {state : ChecksumState} {input : Logical.ByteArray}
    (represented : Represents state input) (bytes : Logical.ByteArray) :
    Represents (account state bytes) (input ++ bytes) := by
  rcases represented with ⟨crc, size⟩
  constructor
  · simp only [account, ← CRC32.updateRaw_eq_maskedUpdateRaw, crc,
      CRC32.updateRaw_append]
  · simp [account, size, BitVec.ofNat_add]

/-- Materialize the two trailer fields using the shared gzip serializer. -/
def trailer (state : ChecksumState) : Gzip.Trailer :=
  ⟨state.rawCrc ^^^ CRC32.initial, state.inputSize⟩

/-- `trailer_of_represents` identifies the CRC and modulo-size values passed
from the implementation state to the container writer. -/
theorem trailer_of_represents {state : ChecksumState} {input : Logical.ByteArray}
    (represented : Represents state input) :
    trailer state = ⟨CRC32.checksum input, BitVec.ofNat 32 input.length⟩ := by
  rcases represented with ⟨crc, size⟩
  simp [trailer, crc, size, CRC32.checksum, CRC32.initial]

/-- `read_written_trailer` composes input accounting with the actual trailer
writer/reader, preserving an arbitrary suffix. -/
theorem read_written_trailer {state : ChecksumState} {input : Logical.ByteArray}
    (represented : Represents state input) (suffix : Logical.ByteArray) :
    Gzip.Trailer.read (Gzip.Trailer.write (trailer state) ++ suffix) =
      .done ⟨CRC32.checksum input, BitVec.ofNat 32 input.length⟩ suffix := by
  rw [Gzip.Trailer.read_write_append, trailer_of_represents represented]

end ChecksumState
end Grass.Std.Zlib.Fixed32K
