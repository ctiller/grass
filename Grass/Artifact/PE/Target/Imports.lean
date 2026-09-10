import Grass.Artifact.Binary.LittleEndian
import Grass.Artifact.PE.Target.Names

/-!
# The PE32+ import directory

The `.idata` payload `Grass.Artifact.PE.format` appends when a program names
loader-filled slots, and the parser that reads it back.

Format authority: Microsoft, PE Format
(<https://learn.microsoft.com/en-us/windows/win32/debug/pe-format>), sections
"The .idata Section", "Import Directory Table", "Import Lookup Table",
"Hint/Name Table" and "Import Address Table".

## Layout

Every offset below is relative to the `.idata` section's own RVA (`base`),
which the format chooses; every stored RVA is `base` plus such an offset,
except `FirstThunk`, which points into the program's own section.

| Region | Extent |
| --- | --- |
| Import Directory Table | `20 * (libraries + 1)`: one `IMAGE_IMPORT_DESCRIPTOR` per library, then the all-zero terminating descriptor |
| padding | to the next 8-byte boundary, so every Import Lookup Table entry is 8-byte aligned |
| Import Lookup Tables | one per library: an 8-byte `IMAGE_THUNK_DATA64` per symbol, then a zero terminator |
| Hint/Name Table | one record per symbol, in library then symbol order: a 2-byte `Hint` of zero, the name, a NUL |
| DLL name strings | one NUL-terminated name per library |

One descriptor's five fields, "Import Directory Table": `OriginalFirstThunk`
is this library's Import Lookup Table; `TimeDateStamp` and `ForwarderChain`
are zero (the image is never bound and forwards nothing); `Name` is this
library's DLL name string; `FirstThunk` is the Import Address Table, which is
**not** in `.idata` — it is the run of slot addresses the program itself
declared, so the addresses the loader writes are the addresses the program's
code reads.

The Hint/Name records are emitted without the even-byte alignment the
specification recommends; the loader does not require it, and the recommendation
would only add a padding byte whose position the parser must also recompute.

## Round trip

`parseIdata` recovers exactly what `writeIdata` emits and nothing else is
attempted: the library count comes from the import directory's own size (data
directory 1), each library's symbol count from its lookup table's zero
terminator, and each name from its NUL. `parseIdata_writeIdata` is the
inverse law, and it needs three things of the input, all of which
`Grass.Artifact.PE.assemble` checks: names are ASCII and NUL-free, the section
address is non-zero, and every stored RVA fits its field.
-/

namespace Grass.Artifact.PE.Target

open Grass.Artifact.Binary

/-- One library's import requirement: the DLL name, the RVA of the Import
Address Table run the program declared, and the symbol names in slot order. -/
structure Library where
  name : String
  iatRva : Nat
  symbols : List String
deriving DecidableEq

/-! ## Extents -/

/-- One Hint/Name record: 2-byte `Hint`, the name, a NUL. -/
def hintNameSize (s : String) : Nat := 3 + s.toList.length

/-- One library's Hint/Name records. -/
def hintNamesSize : List String → Nat
  | [] => 0
  | s :: rest => hintNameSize s + hintNamesSize rest

/-- One library's Import Lookup Table, terminator included. -/
def iltSize (lib : Library) : Nat := 8 * (lib.symbols.length + 1)

/-- Every library's Import Lookup Table. -/
def iltsSize : List Library → Nat
  | [] => 0
  | lib :: rest => iltSize lib + iltsSize rest

/-- Every library's Hint/Name records. -/
def hintNamesTotal : List Library → Nat
  | [] => 0
  | lib :: rest => hintNamesSize lib.symbols + hintNamesTotal rest

/-- One NUL-terminated DLL name string. -/
def dllNameSize (lib : Library) : Nat := lib.name.toList.length + 1

/-- Every DLL name string. -/
def dllNamesSize : List Library → Nat
  | [] => 0
  | lib :: rest => dllNameSize lib + dllNamesSize rest

/-- The Import Directory Table's own size, which data directory 1 records:
one descriptor per library plus the terminating descriptor. -/
def descriptorTableSize (libraryCount : Nat) : Nat := 20 * (libraryCount + 1)

/-- Padding after the descriptor table, so the lookup tables start 8-byte
aligned. -/
def descriptorPad (libraryCount : Nat) : Nat := (8 - descriptorTableSize libraryCount % 8) % 8

/-- Section-relative offset of the first Import Lookup Table. -/
def iltsOffset (libraryCount : Nat) : Nat :=
  descriptorTableSize libraryCount + descriptorPad libraryCount

/-- Section-relative offset of the Hint/Name Table. -/
def hintNamesOffset (libs : List Library) : Nat := iltsOffset libs.length + iltsSize libs

/-- Section-relative offset of the DLL name strings. -/
def dllNamesOffset (libs : List Library) : Nat := hintNamesOffset libs + hintNamesTotal libs

/-- The whole `.idata` payload's size. -/
def idataSize (libs : List Library) : Nat := dllNamesOffset libs + dllNamesSize libs

/-! ## Writer -/

/-- A descriptor's four fields before `FirstThunk`: `OriginalFirstThunk`,
`TimeDateStamp`, `ForwarderChain`, `Name`. -/
def descriptorHead (iltRva nameRva : Nat) : List UInt8 :=
  writeU32LE (UInt32.ofNat iltRva) ++ writeU32LE 0 ++ writeU32LE 0 ++
    writeU32LE (UInt32.ofNat nameRva)

@[simp] theorem length_descriptorHead (iltRva nameRva : Nat) :
    (descriptorHead iltRva nameRva).length = 16 := by simp [descriptorHead]

/-- The terminating all-zero descriptor. -/
def descriptorTerminator : List UInt8 := List.replicate 20 0

@[simp] theorem length_descriptorTerminator : descriptorTerminator.length = 20 := by
  simp [descriptorTerminator]

/-- The Import Directory Table, threading each library's lookup-table and
name-string cursors. -/
def writeDescriptors (base iltCursor nameCursor : Nat) : List Library → List UInt8
  | [] => descriptorTerminator
  | lib :: rest =>
      descriptorHead (base + iltCursor) (base + nameCursor) ++
        writeU32LE (UInt32.ofNat lib.iatRva) ++
        writeDescriptors base (iltCursor + iltSize lib) (nameCursor + dllNameSize lib) rest

@[simp] theorem length_writeDescriptors (base iltCursor nameCursor : Nat) (libs : List Library) :
    (writeDescriptors base iltCursor nameCursor libs).length = descriptorTableSize libs.length := by
  induction libs generalizing iltCursor nameCursor with
  | nil => simp [writeDescriptors, descriptorTableSize]
  | cons lib libs ih => simp [writeDescriptors, ih, descriptorTableSize]; omega

/-- One Import Lookup Table: an entry per symbol pointing at its Hint/Name
record, then the zero terminator. -/
def writeThunks (base cursor : Nat) : List String → List UInt8
  | [] => writeU64LE 0
  | s :: rest =>
      writeU64LE (UInt64.ofNat (base + cursor)) ++ writeThunks base (cursor + hintNameSize s) rest

@[simp] theorem length_writeThunks (base cursor : Nat) (symbols : List String) :
    (writeThunks base cursor symbols).length = 8 * (symbols.length + 1) := by
  induction symbols generalizing cursor with
  | nil => simp [writeThunks]
  | cons s symbols ih => simp [writeThunks, ih]; omega

/-- Every library's Import Lookup Table, threading the Hint/Name cursor. -/
def writeIlts (base hintCursor : Nat) : List Library → List UInt8
  | [] => []
  | lib :: rest =>
      writeThunks base hintCursor lib.symbols ++
        writeIlts base (hintCursor + hintNamesSize lib.symbols) rest

@[simp] theorem length_writeIlts (base hintCursor : Nat) (libs : List Library) :
    (writeIlts base hintCursor libs).length = iltsSize libs := by
  induction libs generalizing hintCursor with
  | nil => simp [writeIlts, iltsSize]
  | cons lib libs ih => simp [writeIlts, ih, iltsSize, iltSize]

/-- One library's Hint/Name records. -/
def writeHintNames : List String → List UInt8
  | [] => []
  | s :: rest => writeU16LE 0 ++ nameBytes s ++ [0] ++ writeHintNames rest

@[simp] theorem length_writeHintNames (symbols : List String) :
    (writeHintNames symbols).length = hintNamesSize symbols := by
  induction symbols with
  | nil => simp [writeHintNames, hintNamesSize]
  | cons s symbols ih => simp [writeHintNames, ih, hintNamesSize, hintNameSize]; omega

/-- Every library's Hint/Name records. -/
def writeLibHintNames : List Library → List UInt8
  | [] => []
  | lib :: rest => writeHintNames lib.symbols ++ writeLibHintNames rest

@[simp] theorem length_writeLibHintNames (libs : List Library) :
    (writeLibHintNames libs).length = hintNamesTotal libs := by
  induction libs with
  | nil => simp [writeLibHintNames, hintNamesTotal]
  | cons lib libs ih => simp [writeLibHintNames, ih, hintNamesTotal]

/-- The DLL name strings. -/
def writeDllNames : List Library → List UInt8
  | [] => []
  | lib :: rest => nameBytes lib.name ++ [0] ++ writeDllNames rest

@[simp] theorem length_writeDllNames (libs : List Library) :
    (writeDllNames libs).length = dllNamesSize libs := by
  induction libs with
  | nil => simp [writeDllNames, dllNamesSize]
  | cons lib libs ih => simp [writeDllNames, ih, dllNamesSize, dllNameSize]; omega

/-- The complete `.idata` payload for a section placed at `base`. -/
def writeIdata (base : Nat) (libs : List Library) : List UInt8 :=
  writeDescriptors base (iltsOffset libs.length) (dllNamesOffset libs) libs ++
    List.replicate (descriptorPad libs.length) 0 ++
    writeIlts base (hintNamesOffset libs) libs ++ writeLibHintNames libs ++ writeDllNames libs

@[simp] theorem length_writeIdata (base : Nat) (libs : List Library) :
    (writeIdata base libs).length = idataSize libs := by
  simp only [writeIdata, List.length_append, List.length_replicate, length_writeDescriptors,
    length_writeIlts, length_writeLibHintNames, length_writeDllNames, idataSize, dllNamesOffset,
    hintNamesOffset, iltsOffset]

/-! ## Parser -/

/-- Read the descriptors' `FirstThunk` values, then the terminator. The count
comes from data directory 1's size, so no descriptor field has to be trusted
to decide where the table ends. -/
def parseDescriptors : Nat → List UInt8 → Option (List Nat × List UInt8)
  | 0, bytes =>
      match takeBytes 20 bytes with
      | none => none
      | some (_terminator, rest) => some ([], rest)
  | n + 1, bytes =>
      match takeBytes 16 bytes with
      | none => none
      | some (_head, bytes) =>
      match readU32LE bytes with
      | none => none
      | some (iatRva, bytes) =>
      match parseDescriptors n bytes with
      | none => none
      | some (tail, rest) => some (iatRva.toNat :: tail, rest)

/-- Count one Import Lookup Table's entries, stopping at the zero terminator.
`fuel` bounds the scan; `parseThunks` supplies the remaining byte count, which
is always more than the entries there can be. -/
def parseThunksAux : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _ => none
  | fuel + 1, bytes =>
      match readU64LE bytes with
      | none => none
      | some (entry, bytes) =>
          if entry = 0 then some (0, bytes)
          else
            match parseThunksAux fuel bytes with
            | none => none
            | some (count, rest) => some (count + 1, rest)

/-- Count one Import Lookup Table's entries. -/
def parseThunks (bytes : List UInt8) : Option (Nat × List UInt8) := parseThunksAux bytes.length bytes

/-- Each library's symbol count, from its lookup table. -/
def parseIlts : Nat → List UInt8 → Option (List Nat × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes =>
      match parseThunks bytes with
      | none => none
      | some (count, bytes) =>
      match parseIlts n bytes with
      | none => none
      | some (tail, rest) => some (count :: tail, rest)

/-- One library's Hint/Name records. -/
def parseHintNames : Nat → List UInt8 → Option (List String × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes =>
      match takeBytes 2 bytes with
      | none => none
      | some (_hint, bytes) =>
      match parseCString bytes with
      | none => none
      | some (name, bytes) =>
      match parseHintNames n bytes with
      | none => none
      | some (tail, rest) => some (decodeName name :: tail, rest)

/-- Every library's Hint/Name records, grouped by the symbol counts the lookup
tables gave. -/
def parseLibHintNames : List Nat → List UInt8 → Option (List (List String) × List UInt8)
  | [], bytes => some ([], bytes)
  | count :: counts, bytes =>
      match parseHintNames count bytes with
      | none => none
      | some (names, bytes) =>
      match parseLibHintNames counts bytes with
      | none => none
      | some (tail, rest) => some (names :: tail, rest)

/-- The DLL name strings. -/
def parseDllNames : Nat → List UInt8 → Option (List String × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes =>
      match parseCString bytes with
      | none => none
      | some (name, bytes) =>
      match parseDllNames n bytes with
      | none => none
      | some (tail, rest) => some (decodeName name :: tail, rest)

/-- Recombine the three parallel recoveries into libraries. -/
def zipLibraries : List Nat → List (List String) → List String → List Library
  | [], _, _ => []
  | _ :: _, [], _ => []
  | _ :: _, _ :: _, [] => []
  | iat :: iats, symbols :: symbolGroups, name :: names =>
      { name, iatRva := iat, symbols } :: zipLibraries iats symbolGroups names

/-- Recover the import requirement from an `.idata` payload, given the library
count data directory 1's size records. -/
def parseIdata (libraryCount : Nat) (bytes : List UInt8) : Option (List Library) :=
  match parseDescriptors libraryCount bytes with
  | none => none
  | some (iatRvas, bytes) =>
  match takeBytes (descriptorPad libraryCount) bytes with
  | none => none
  | some (_pad, bytes) =>
  match parseIlts libraryCount bytes with
  | none => none
  | some (counts, bytes) =>
  match parseLibHintNames counts bytes with
  | none => none
  | some (symbolGroups, bytes) =>
  match parseDllNames libraryCount bytes with
  | none => none
  | some (names, _rest) => some (zipLibraries iatRvas symbolGroups names)

/-! ## The inverse law -/

/-- The descriptors' `FirstThunk` values are recovered exactly, for the exact
library count, with the exact byte suffix. -/
theorem parseDescriptors_writeDescriptors (base iltCursor nameCursor : Nat)
    (libs : List Library) (rest : List UInt8)
    (bound : ∀ lib ∈ libs, lib.iatRva < 4294967296) :
    parseDescriptors libs.length (writeDescriptors base iltCursor nameCursor libs ++ rest) =
      some (libs.map fun lib => lib.iatRva, rest) := by
  induction libs generalizing iltCursor nameCursor with
  | nil =>
      simp only [List.length_nil, writeDescriptors, parseDescriptors,
        takeBytes_append_of_eq length_descriptorTerminator, List.map_nil]
  | cons lib libs ih =>
      have iatEq : (UInt32.ofNat lib.iatRva).toNat = lib.iatRva := by
        rw [UInt32.toNat_ofNat']
        exact Nat.mod_eq_of_lt (bound lib (List.mem_cons_self ..))
      have shape : writeDescriptors base iltCursor nameCursor (lib :: libs) ++ rest =
          descriptorHead (base + iltCursor) (base + nameCursor) ++
            (writeU32LE (UInt32.ofNat lib.iatRva) ++
              (writeDescriptors base (iltCursor + iltSize lib) (nameCursor + dllNameSize lib) libs ++
                rest)) := by
        simp [writeDescriptors, List.append_assoc]
      rw [List.length_cons, shape]
      simp only [parseDescriptors, takeBytes_append_of_eq (length_descriptorHead _ _),
        readU32LE_writeU32LE_append, iatEq,
        ih (iltCursor + iltSize lib) (nameCursor + dllNameSize lib)
          (fun l member => bound l (List.mem_cons_of_mem _ member)),
        List.map_cons]

/-- A lookup table's entries are counted exactly: every entry this writer emits
is a non-zero RVA, so the zero terminator is the only stop. -/
theorem parseThunksAux_writeThunks (base cursor fuel : Nat) (symbols : List String)
    (rest : List UInt8) (positive : 0 < base)
    (bound : base + cursor + hintNamesSize symbols < 18446744073709551616)
    (enough : symbols.length < fuel) :
    parseThunksAux fuel (writeThunks base cursor symbols ++ rest) = some (symbols.length, rest) := by
  induction symbols generalizing cursor fuel with
  | nil =>
      cases fuel with
      | zero => omega
      | succ f =>
          simp only [writeThunks, parseThunksAux, readU64LE_writeU64LE_append, ↓reduceIte,
            List.length_nil]
  | cons s symbols ih =>
      cases fuel with
      | zero => omega
      | succ f =>
          have entryBound : base + cursor < 18446744073709551616 := by
            have : 0 ≤ hintNamesSize (s :: symbols) := Nat.zero_le _
            omega
          have entryEq : (UInt64.ofNat (base + cursor)).toNat = base + cursor := by
            rw [UInt64.toNat_ofNat']
            exact Nat.mod_eq_of_lt entryBound
          have nonzero : UInt64.ofNat (base + cursor) ≠ 0 := by
            intro zero
            rw [zero] at entryEq
            simp only [UInt64.toNat_ofNat, Nat.zero_mod] at entryEq
            omega
          have tailBound : base + (cursor + hintNameSize s) + hintNamesSize symbols <
              18446744073709551616 := by
            have expand : hintNamesSize (s :: symbols) = hintNameSize s + hintNamesSize symbols :=
              rfl
            omega
          have shape : writeThunks base cursor (s :: symbols) ++ rest =
              writeU64LE (UInt64.ofNat (base + cursor)) ++
                (writeThunks base (cursor + hintNameSize s) symbols ++ rest) := by
            simp [writeThunks, List.append_assoc]
          rw [shape]
          simp only [parseThunksAux, readU64LE_writeU64LE_append, nonzero, ↓reduceIte,
            ih (cursor + hintNameSize s) f tailBound (by simpa using Nat.lt_of_succ_lt_succ enough),
            List.length_cons]

/-- The fuel-free form: the remaining byte count always exceeds the entry
count, since each entry is eight bytes. -/
theorem parseThunks_writeThunks (base cursor : Nat) (symbols : List String) (rest : List UInt8)
    (positive : 0 < base)
    (bound : base + cursor + hintNamesSize symbols < 18446744073709551616) :
    parseThunks (writeThunks base cursor symbols ++ rest) = some (symbols.length, rest) := by
  unfold parseThunks
  refine parseThunksAux_writeThunks base cursor _ symbols rest positive bound ?_
  simp only [List.length_append, length_writeThunks]
  omega

/-- Every library's symbol count is recovered exactly, with the exact byte
suffix. -/
theorem parseIlts_writeIlts (base hintCursor : Nat) (libs : List Library) (rest : List UInt8)
    (positive : 0 < base)
    (bound : base + hintCursor + hintNamesTotal libs < 18446744073709551616) :
    parseIlts libs.length (writeIlts base hintCursor libs ++ rest) =
      some (libs.map fun lib => lib.symbols.length, rest) := by
  induction libs generalizing hintCursor with
  | nil => simp only [List.length_nil, writeIlts, List.nil_append, parseIlts, List.map_nil]
  | cons lib libs ih =>
      have expand : hintNamesTotal (lib :: libs) =
          hintNamesSize lib.symbols + hintNamesTotal libs := rfl
      have headBound : base + hintCursor + hintNamesSize lib.symbols <
          18446744073709551616 := by omega
      have tailBound : base + (hintCursor + hintNamesSize lib.symbols) + hintNamesTotal libs <
          18446744073709551616 := by omega
      have shape : writeIlts base hintCursor (lib :: libs) ++ rest =
          writeThunks base hintCursor lib.symbols ++
            (writeIlts base (hintCursor + hintNamesSize lib.symbols) libs ++ rest) := by
        simp [writeIlts, List.append_assoc]
      rw [List.length_cons, shape]
      simp only [parseIlts, parseThunks_writeThunks base hintCursor lib.symbols _ positive headBound,
        ih (hintCursor + hintNamesSize lib.symbols) tailBound, List.map_cons]

/-- One library's symbol names are recovered exactly, with the exact byte
suffix. -/
theorem parseHintNames_writeHintNames (symbols : List String) (rest : List UInt8)
    (ascii : ∀ s ∈ symbols, AsciiName s) :
    parseHintNames symbols.length (writeHintNames symbols ++ rest) = some (symbols, rest) := by
  induction symbols with
  | nil => simp only [List.length_nil, writeHintNames, List.nil_append, parseHintNames]
  | cons s symbols ih =>
      have here : s ∈ s :: symbols := List.mem_cons_self ..
      have shape : writeHintNames (s :: symbols) ++ rest =
          writeU16LE 0 ++ (nameBytes s ++ (0 :: (writeHintNames symbols ++ rest))) := by
        simp [writeHintNames, List.append_assoc]
      rw [List.length_cons, shape]
      simp only [parseHintNames, takeBytes_writeU16LE_append,
        parseCString_append (nameBytes_ne_zero (ascii s here)),
        decodeName_nameBytes (ascii s here),
        ih (fun t member => ascii t (List.mem_cons_of_mem _ member))]

/-- Every library's symbol names are recovered exactly, grouped as the lookup
tables said. -/
theorem parseLibHintNames_writeLibHintNames (libs : List Library) (rest : List UInt8)
    (ascii : ∀ lib ∈ libs, ∀ s ∈ lib.symbols, AsciiName s) :
    parseLibHintNames (libs.map fun lib => lib.symbols.length) (writeLibHintNames libs ++ rest) =
      some (libs.map fun lib => lib.symbols, rest) := by
  induction libs with
  | nil => simp only [List.map_nil, writeLibHintNames, List.nil_append, parseLibHintNames]
  | cons lib libs ih =>
      have shape : writeLibHintNames (lib :: libs) ++ rest =
          writeHintNames lib.symbols ++ (writeLibHintNames libs ++ rest) := by
        simp [writeLibHintNames, List.append_assoc]
      rw [List.map_cons, shape]
      simp only [parseLibHintNames,
        parseHintNames_writeHintNames lib.symbols _ (ascii lib (List.mem_cons_self ..)),
        ih (fun l member => ascii l (List.mem_cons_of_mem _ member)), List.map_cons]

/-- The DLL names are recovered exactly. -/
theorem parseDllNames_writeDllNames (libs : List Library) (rest : List UInt8)
    (ascii : ∀ lib ∈ libs, AsciiName lib.name) :
    parseDllNames libs.length (writeDllNames libs ++ rest) =
      some (libs.map fun lib => lib.name, rest) := by
  induction libs with
  | nil => simp only [List.length_nil, writeDllNames, List.nil_append, parseDllNames, List.map_nil]
  | cons lib libs ih =>
      have here : lib ∈ lib :: libs := List.mem_cons_self ..
      have shape : writeDllNames (lib :: libs) ++ rest =
          nameBytes lib.name ++ (0 :: (writeDllNames libs ++ rest)) := by
        simp [writeDllNames, List.append_assoc]
      rw [List.length_cons, shape]
      simp only [parseDllNames, parseCString_append (nameBytes_ne_zero (ascii lib here)),
        decodeName_nameBytes (ascii lib here),
        ih (fun l member => ascii l (List.mem_cons_of_mem _ member)), List.map_cons]

/-- The no-trailing-bytes instance: the DLL name strings end the payload. -/
theorem parseDllNames_writeDllNames_nil (libs : List Library)
    (ascii : ∀ lib ∈ libs, AsciiName lib.name) :
    parseDllNames libs.length (writeDllNames libs) = some (libs.map fun lib => lib.name, []) := by
  simpa using parseDllNames_writeDllNames libs [] ascii

/-- The three parallel recoveries recombine into the libraries they came
from. -/
theorem zipLibraries_maps (libs : List Library) :
    zipLibraries (libs.map fun lib => lib.iatRva) (libs.map fun lib => lib.symbols)
      (libs.map fun lib => lib.name) = libs := by
  induction libs with
  | nil => rfl
  | cons lib libs ih => simp [zipLibraries, ih]

/-- The parser inverts the writer exactly: an `.idata` payload this format
emitted gives back the exact import requirement it was built from. -/
theorem parseIdata_writeIdata (base : Nat) (libs : List Library) (positive : 0 < base)
    (bound : base + idataSize libs < 18446744073709551616)
    (iatBound : ∀ lib ∈ libs, lib.iatRva < 4294967296)
    (nameAscii : ∀ lib ∈ libs, AsciiName lib.name)
    (symbolAscii : ∀ lib ∈ libs, ∀ s ∈ lib.symbols, AsciiName s) :
    parseIdata libs.length (writeIdata base libs) = some libs := by
  have iltsBound : base + hintNamesOffset libs + hintNamesTotal libs <
      18446744073709551616 := by
    have expand : idataSize libs = hintNamesOffset libs + hintNamesTotal libs + dllNamesSize libs :=
      rfl
    omega
  have padLength :
      (List.replicate (descriptorPad libs.length) (0 : UInt8)).length =
        descriptorPad libs.length := List.length_replicate ..
  simp only [writeIdata, List.append_assoc]
  unfold parseIdata
  simp only [parseDescriptors_writeDescriptors base (iltsOffset libs.length) (dllNamesOffset libs)
      libs _ iatBound,
    takeBytes_append_of_eq padLength,
    parseIlts_writeIlts base (hintNamesOffset libs) libs _ positive iltsBound,
    parseLibHintNames_writeLibHintNames libs _ symbolAscii,
    parseDllNames_writeDllNames_nil libs nameAscii, zipLibraries_maps]

/-- The append form: an `.idata` payload this format emitted, followed by
arbitrary trailing bytes (the empty base-relocation block `.idata` now carries
after its own content, `Grass.Artifact.PE.idataSection`), still gives back the
exact import requirement, with the trailing bytes discarded rather than
required to be empty. -/
theorem parseIdata_writeIdata_append (base : Nat) (libs : List Library) (rest : List UInt8)
    (positive : 0 < base)
    (bound : base + idataSize libs < 18446744073709551616)
    (iatBound : ∀ lib ∈ libs, lib.iatRva < 4294967296)
    (nameAscii : ∀ lib ∈ libs, AsciiName lib.name)
    (symbolAscii : ∀ lib ∈ libs, ∀ s ∈ lib.symbols, AsciiName s) :
    parseIdata libs.length (writeIdata base libs ++ rest) = some libs := by
  have iltsBound : base + hintNamesOffset libs + hintNamesTotal libs <
      18446744073709551616 := by
    have expand : idataSize libs = hintNamesOffset libs + hintNamesTotal libs + dllNamesSize libs :=
      rfl
    omega
  have padLength :
      (List.replicate (descriptorPad libs.length) (0 : UInt8)).length =
        descriptorPad libs.length := List.length_replicate ..
  simp only [writeIdata, List.append_assoc]
  unfold parseIdata
  simp only [parseDescriptors_writeDescriptors base (iltsOffset libs.length) (dllNamesOffset libs)
      libs _ iatBound,
    takeBytes_append_of_eq padLength,
    parseIlts_writeIlts base (hintNamesOffset libs) libs _ positive iltsBound,
    parseLibHintNames_writeLibHintNames libs _ symbolAscii,
    parseDllNames_writeDllNames libs rest nameAscii, zipLibraries_maps]

end Grass.Artifact.PE.Target
