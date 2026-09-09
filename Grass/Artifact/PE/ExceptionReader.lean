import Grass.Artifact.PE.ReaderCore
import Grass.Artifact.PE.Exceptions

/-! Independent decoding of PE32+ runtime-function table fields.
Parsing does not establish that a record's targets are valid unwind metadata. -/
namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical Grass.Artifact.Binary

/-- The three image-relative DWORD fields of an AMD64 runtime-function record. -/
structure ParsedRuntimeFunction where
  beginRva : BitVec 32
  endRva : BitVec 32
  unwindRva : BitVec 32
deriving DecidableEq, Repr

/-- Decode one complete record, retaining its unconsumed suffix. -/
def readRuntimeFunction (input : Std.Logical.ByteArray) : ParseResult ParsedRuntimeFunction :=
  continueRead (takeLittleEndian 4 input) fun beginRva input =>
  continueRead (takeLittleEndian 4 input) fun endRva input =>
  continueRead (takeLittleEndian 4 input) fun unwindRva input =>
  .done ⟨beginRva, endRva, unwindRva⟩ input

/-- Decode a caller-selected count. The whole-table entry point derives this
count from the supplied byte extent. -/
def readRuntimeFunctions : Nat → Std.Logical.ByteArray → ParseResult (List ParsedRuntimeFunction)
  | 0, input => .done [] input
  | count + 1, input =>
      continueRead (readRuntimeFunction input) fun head rest =>
      continueRead (readRuntimeFunctions count rest) fun tail rest => .done (head :: tail) rest

/-- Read an exact table extent; incomplete record lengths are rejected. -/
def readRuntimeTable (input : Std.Logical.ByteArray) : ParseResult (List ParsedRuntimeFunction) :=
  if input.length % 12 = 0 then readRuntimeFunctions (input.length / 12) input
  else .invalid (.malformed "PE runtime table extent is not a multiple of 12")

/-- Exact serialized field values; resolver bounds establish lossless narrowing. -/
def ResolvedRuntimeFunction.expectedRecord (function : ResolvedRuntimeFunction) :
    ParsedRuntimeFunction :=
  ⟨BitVec.ofNat 32 function.beginRva, BitVec.ofNat 32 function.endRva,
    BitVec.ofNat 32 function.unwindRva⟩

/-- Successful runtime resolution makes every decoded DWORD lossless. -/
theorem ResolvedRuntimeFunction.expectedRecord_exact {placed : Vec PlacedSection}
    {binding : RuntimeFunctionBinding} {function : ResolvedRuntimeFunction}
    (resolved : resolveRuntimeFunction? placed binding = some function) :
    function.expectedRecord.beginRva.toNat = function.beginRva ∧
    function.expectedRecord.endRva.toNat = function.endRva ∧
    function.expectedRecord.unwindRva.toNat = function.unwindRva := by
  have bounds := resolveRuntimeFunction?_bounds resolved
  simp [expectedRecord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounds.1,
    Nat.mod_eq_of_lt bounds.2.1, Nat.mod_eq_of_lt bounds.2.2]

/-- Independently decode all three fields and preserve any suffix. -/
theorem readRuntimeFunction_write_append (function : ResolvedRuntimeFunction)
    (suffix : Std.Logical.ByteArray) :
    readRuntimeFunction (writeRuntimeFunction function ++ suffix) =
      .done function.expectedRecord suffix := by
  simp [readRuntimeFunction, writeRuntimeFunction, Vec.append_assoc,
    takeLittleEndian_writeLittleEndian_append, continueRead,
    ResolvedRuntimeFunction.expectedRecord]

/-- The independent table reader recovers every record in order. -/
theorem readRuntimeFunctions_write_append (functions : List ResolvedRuntimeFunction)
    (suffix : Std.Logical.ByteArray) :
    readRuntimeFunctions functions.length (writeRuntimeFunctions functions ++ suffix) =
      .done (functions.map ResolvedRuntimeFunction.expectedRecord) suffix := by
  induction functions with
  | nil => simp [readRuntimeFunctions, writeRuntimeFunctions]
  | cons head tail ih =>
      simp only [List.length_cons, writeRuntimeFunctions, readRuntimeFunctions,
        Vec.append_assoc, readRuntimeFunction_write_append, continueRead, ih, List.map_cons]

/-- Exact meaningful table bytes determine the record count without caller input. -/
theorem readRuntimeTable_write (functions : List ResolvedRuntimeFunction) :
    readRuntimeTable (writeRuntimeFunctions functions) =
      .done (functions.map ResolvedRuntimeFunction.expectedRecord) Vec.empty := by
  unfold readRuntimeTable
  rw [length_writeRuntimeFunctions]
  simp only [Nat.mul_mod_right, if_true]
  simpa using readRuntimeFunctions_write_append functions Vec.empty

end Grass.Artifact.PE
