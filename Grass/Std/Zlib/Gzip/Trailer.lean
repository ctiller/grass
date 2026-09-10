import Grass.Artifact.Binary.EndianLaws

/-!
# Gzip trailer serialization

RFC 1952 sections 2.1 and 2.3.1 specify CRC32 followed by ISIZE, both
little-endian words. The reader handles the trailer at an already established
DEFLATE boundary; it does not locate that boundary or validate the checksum
against a decoded payload. See https://www.rfc-editor.org/rfc/rfc1952.html.
-/

namespace Grass.Std.Zlib.Gzip

open Grass.Std.Logical Grass.Grammar Grass.Artifact.Binary

/-- The two values carried by the eight-byte gzip trailer. -/
structure Trailer where
  crc32 : BitVec 32
  inputSize : BitVec 32
deriving DecidableEq, Repr

namespace Trailer

/-- Emit the CRC word before the input-size word, as specified by RFC 1952. -/
def write (trailer : Trailer) : Logical.ByteArray :=
  writeLittleEndian (count := 4) trailer.crc32 ++
    writeLittleEndian (count := 4) trailer.inputSize

/-- `length_write` computes the trailer's fixed byte width. -/
@[simp] theorem length_write (trailer : Trailer) : (write trailer).length = 8 := by
  simp [write]

/-- Read both little-endian fields, reporting the whole trailer deficit before
attempting either field. This avoids a four-byte hint for an eight-byte record. -/
def read (input : Logical.ByteArray) : ParseResult Trailer :=
  if input.length < 8 then .needMore (some (8 - input.length))
  else
    match takeLittleEndian 4 input with
    | .done crc rest =>
      match takeLittleEndian 4 rest with
      | .done size suffix => .done ⟨crc, size⟩ suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    | .needMore hint => .needMore hint
    | .invalid error => .invalid error

/-- `read_write_append` retains the exact arbitrary suffix after a trailer. -/
@[simp] theorem read_write_append (trailer : Trailer) (suffix : Logical.ByteArray) :
    read (write trailer ++ suffix) = .done trailer suffix := by
  simp [read, write, Vec.append_assoc]
  omega

/-- `read_write` is the complete-input trailer round trip. -/
@[simp] theorem read_write (trailer : Trailer) :
    read (write trailer) = .done trailer Vec.empty := by
  simpa using read_write_append trailer Vec.empty

/-- `read_short` returns the exact number of bytes needed to complete a trailer. -/
theorem read_short {input : Logical.ByteArray} (short : input.length < 8) :
    read input = .needMore (some (8 - input.length)) := by
  simp [read, short]

/-- `read_enough` proves that every complete trailer is accepted, irrespective
of the bit patterns in its two fields. Payload validation is a later operation. -/
theorem read_enough {input : Logical.ByteArray} (enough : 8 ≤ input.length) :
    ∃ trailer rest, read input = .done trailer rest := by
  have firstEnough : 4 ≤ input.length := by omega
  have secondEnough : 4 ≤ input.length - 4 := by omega
  simp [read, Nat.not_lt.mpr enough, takeLittleEndian, isoParser,
    takeExactSized, firstEnough, secondEnough, ParseResult.map]

/-- `read_needMore_iff` gives the exact complete-record deficit and rules out
incomplete classifications on all sufficiently long inputs. -/
theorem read_needMore_iff (input : Logical.ByteArray) (hint : Option Nat) :
    read input = .needMore hint ↔ input.length < 8 ∧ hint = some (8 - input.length) := by
  by_cases short : input.length < 8
  · simp [read_short short, short, eq_comm]
  · obtain ⟨trailer, rest, parsed⟩ := read_enough (Nat.le_of_not_gt short)
    simp [parsed, short]

/-- `read_done` reconstructs every successful trailer and its exact suffix. -/
theorem read_done {input rest : Logical.ByteArray} {trailer : Trailer}
    (parsed : read input = .done trailer rest) : input = write trailer ++ rest := by
  unfold read at parsed
  split at parsed
  · contradiction
  · split at parsed
    next crc remaining first =>
      split at parsed
      next size suffix second =>
        cases parsed
        rw [takeLittleEndian_done first, takeLittleEndian_done second]
        simp [write, Vec.append_assoc]
      all_goals contradiction
    all_goals contradiction

/-- `read_exact` characterizes accepted bytes, not merely emitted examples. -/
theorem read_exact (input rest : Logical.ByteArray) (trailer : Trailer) :
    read input = .done trailer rest ↔ input = write trailer ++ rest := by
  constructor
  · exact read_done
  · intro encoded
    rw [encoded]
    exact read_write_append trailer rest

end Trailer
end Grass.Std.Zlib.Gzip
