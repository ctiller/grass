import Grass.Artifact.Binary.ReaderCore

/-! # ELF64 little-endian program header fields

Structural serialization only. Authority: System V generic ABI, Program Header,
https://gabi.xinuos.com/elf/07-pheader.html (accessed 2026-09-09).
The reader retains every field but does not validate segment type, alignment,
range, ordering, or loadability.
-/

namespace Grass.Artifact.ELF

open Grass.Std.Logical Grass.Grammar Grass.Artifact.Binary

/-- Complete ELF64 program-header fields in their on-disk order. -/
structure ProgramHeader64 where
  segmentType : BitVec 32
  flags : BitVec 32
  offset : BitVec 64
  virtualAddress : BitVec 64
  physicalAddress : BitVec 64
  fileSize : BitVec 64
  memorySize : BitVec 64
  alignment : BitVec 64
deriving DecidableEq, Repr

/-- Serialize one structural ELF64 program header in the selected byte order. -/
def writeProgramHeader64 (header : ProgramHeader64) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) header.segmentType ++
    writeLittleEndian (count := 4) header.flags ++
    writeLittleEndian (count := 8) header.offset ++
    writeLittleEndian (count := 8) header.virtualAddress ++
    writeLittleEndian (count := 8) header.physicalAddress ++
    writeLittleEndian (count := 8) header.fileSize ++
    writeLittleEndian (count := 8) header.memorySize ++
    writeLittleEndian (count := 8) header.alignment

/-- Read all fields under the selected ELF64 little-endian program-header layout. -/
def readProgramHeader64 (input : Std.Logical.ByteArray) : ParseResult ProgramHeader64 :=
  continueRead (takeLittleEndian 4 input) fun segmentType input =>
  continueRead (takeLittleEndian 4 input) fun flags input =>
  continueRead (takeLittleEndian 8 input) fun offset input =>
  continueRead (takeLittleEndian 8 input) fun virtualAddress input =>
  continueRead (takeLittleEndian 8 input) fun physicalAddress input =>
  continueRead (takeLittleEndian 8 input) fun fileSize input =>
  continueRead (takeLittleEndian 8 input) fun memorySize input =>
  continueRead (takeLittleEndian 8 input) fun alignment input =>
  .done (ProgramHeader64.mk segmentType flags offset virtualAddress physicalAddress
    fileSize memorySize alignment) input

@[simp] theorem writeProgramHeader64_length (header : ProgramHeader64) :
    (writeProgramHeader64 header).length = 56 := by
  simp [writeProgramHeader64]

/-- Writing one program header before any suffix is read back exactly. -/
theorem readProgramHeader64_write_append (header : ProgramHeader64)
    (suffix : Std.Logical.ByteArray) :
    readProgramHeader64 (writeProgramHeader64 header ++ suffix) = .done header suffix := by
  simp [readProgramHeader64, writeProgramHeader64, Vec.append_assoc, continueRead]

/-- A successful structural read consumes exactly one serialized program header. -/
theorem readProgramHeader64_done {input rest : Std.Logical.ByteArray}
    {header : ProgramHeader64}
    (success : readProgramHeader64 input = .done header rest) :
    input = writeProgramHeader64 header ++ rest := by
  unfold readProgramHeader64 continueRead at success
  cases segmentTypeResult : takeLittleEndian 4 input <;>
    simp [segmentTypeResult] at success
  case done segmentType rest0 =>
    cases flagsResult : takeLittleEndian 4 rest0 <;> simp [flagsResult] at success
    case done flags rest1 =>
      cases offsetResult : takeLittleEndian 8 rest1 <;> simp [offsetResult] at success
      case done offset rest2 =>
        cases virtualAddressResult : takeLittleEndian 8 rest2 <;>
          simp [virtualAddressResult] at success
        case done virtualAddress rest3 =>
          cases physicalAddressResult : takeLittleEndian 8 rest3 <;>
            simp [physicalAddressResult] at success
          case done physicalAddress rest4 =>
            cases fileSizeResult : takeLittleEndian 8 rest4 <;>
              simp [fileSizeResult] at success
            case done fileSize rest5 =>
              cases memorySizeResult : takeLittleEndian 8 rest5 <;>
                simp [memorySizeResult] at success
              case done memorySize rest6 =>
                cases alignmentResult : takeLittleEndian 8 rest6 <;>
                  simp [alignmentResult] at success
                case done alignment rest7 =>
                  rcases success with ⟨headerEq, restEq⟩
                  subst header
                  subst rest
                  have segmentTypeConsumed := takeLittleEndian_done segmentTypeResult
                  have flagsConsumed := takeLittleEndian_done flagsResult
                  have offsetConsumed := takeLittleEndian_done offsetResult
                  have virtualAddressConsumed := takeLittleEndian_done virtualAddressResult
                  have physicalAddressConsumed := takeLittleEndian_done physicalAddressResult
                  have fileSizeConsumed := takeLittleEndian_done fileSizeResult
                  have memorySizeConsumed := takeLittleEndian_done memorySizeResult
                  have alignmentConsumed := takeLittleEndian_done alignmentResult
                  rw [segmentTypeConsumed, flagsConsumed, offsetConsumed,
                    virtualAddressConsumed, physicalAddressConsumed, fileSizeConsumed,
                    memorySizeConsumed, alignmentConsumed]
                  simp [writeProgramHeader64, Vec.append_assoc]

/-- A successful structural read advances by exactly one ELF64 program header. -/
theorem readProgramHeader64_consumes56 {input rest : Std.Logical.ByteArray}
    {header : ProgramHeader64}
    (success : readProgramHeader64 input = .done header rest) :
    input.length = 56 + rest.length := by
  rw [readProgramHeader64_done success]
  simp

end Grass.Artifact.ELF
