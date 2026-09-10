import Grass.Artifact.ELF.LoadPlan

set_option maxRecDepth 100000

namespace Tests.Artifact.ELF.LoadPlan

open Grass.Artifact.ELF Grass.Std.Logical

def profile : LoadProfile :=
  { machine := 183, pageSize := 0x1000, userStart := 0x400000,
    userLimit := 0x500000, maxMappedBytes := 16 }

def elfHeader (count : BitVec 16 := 1) (entry : BitVec 64 := 0x400000)
    (programOffset : BitVec 64 := 64) : Header64 where
  ident := ident64LE
  objectType := 2
  machine := 183
  version := 1
  entry := entry
  programOffset := programOffset
  sectionOffset := 0
  flags := 0
  headerSize := 64
  programEntrySize := 56
  programCount := count
  sectionEntrySize := 0
  sectionCount := 0
  stringSectionIndex := 0

def load (flags : BitVec 32 := 5) (fileSize : BitVec 64 := 2)
    (memorySize : BitVec 64 := 4) (virtualAddress : BitVec 64 := 0x400000)
    (alignment : BitVec 64 := 0x1000) : ProgramHeader64 :=
  ProgramHeader64.mk 1 flags 0x1000 virtualAddress 0 fileSize memorySize alignment

def imageWith (header : Header64) (programs : List ProgramHeader64)
    (payload : Grass.Std.Logical.ByteArray := Vec.fromList [0xa5, 0x5a]) : Grass.Std.Logical.ByteArray :=
  let headerBytes := writeHeader64 header ++ programs.foldr (fun p rest => writeProgramHeader64 p ++ rest) Vec.empty
  headerBytes ++ Vec.replicate (0x1000 - headerBytes.length) 0 ++ payload

def image : Grass.Std.Logical.ByteArray := imageWith (elfHeader) [load]

example : (plan? profile image).isSome := by decide

example : segmentBytes image (load) = Vec.fromList [0xa5, 0x5a, 0, 0] := by decide

/-- Unrecognized dynamic/interpreter entries are outside this PT_LOAD/PT_NULL profile. -/
example : (plan? profile (imageWith (elfHeader) [{ load with segmentType := 2 }])).isNone := by decide
example : (plan? profile (imageWith (elfHeader) [{ load with segmentType := 3 }])).isNone := by decide

example : (plan? profile (imageWith (elfHeader) [load (fileSize := 5) (memorySize := 4)])).isNone := by decide
example : (plan? profile (imageWith (elfHeader) [load (virtualAddress := 0x500000)])).isNone := by decide
example : (plan? profile (imageWith (elfHeader) [load (flags := 8)])).isNone := by decide
example : (plan? profile (imageWith (elfHeader) [load (alignment := 3)])).isNone := by decide
example : (plan? profile (imageWith (elfHeader) [load (flags := 4)])).isNone := by decide
example : (plan? { profile with maxMappedBytes := 3 } image).isNone := by decide

/-- The table offset must name complete bytes in the actual file. -/
example : (plan? profile (imageWith (elfHeader (programOffset := 0x2000)) [load])).isNone := by decide

/-- Header count and the parsed table agree; a truncated table cannot acquire a plan. -/
example :
    (plan? profile (writeHeader64 (elfHeader 2) ++ writeProgramHeader64 load)).isNone := by decide

def overlapping : Grass.Std.Logical.ByteArray :=
  imageWith (elfHeader 2) [load, { load with virtualAddress := 0x400002 }]

example : (plan? profile overlapping).isNone := by decide

end Tests.Artifact.ELF.LoadPlan
