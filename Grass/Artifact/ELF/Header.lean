import Grass.Artifact.Binary.ReaderCore

/-! # ELF64 little-endian header fields

Structural serialization, independent of OS and instruction execution.
Authority: System V generic ABI, ELF Header,
https://gabi.xinuos.com/elf/02-eheader.html (accessed 2026-09-09).
The raw reader retains every field; the selected reader checks the canonical
identification, version and header size.
Neither reader validates program/section tables or certifies loadability.
-/

namespace Grass.Artifact.ELF
open Grass.Std.Logical Grass.Grammar Grass.Artifact.Binary

/-- Complete ELF64 header fields, including identification and reserved bytes. -/
structure Header64 where
  ident : SizedByteArray 16
  objectType : BitVec 16
  machine : BitVec 16
  version : BitVec 32
  entry : BitVec 64
  programOffset : BitVec 64
  sectionOffset : BitVec 64
  flags : BitVec 32
  headerSize : BitVec 16
  programEntrySize : BitVec 16
  programCount : BitVec 16
  sectionEntrySize : BitVec 16
  sectionCount : BitVec 16
  stringSectionIndex : BitVec 16
deriving DecidableEq, Repr

/-- Canonical ELF64 little-endian identification with no OS-specific extension. -/
def ident64LE : SizedByteArray 16 :=
  ⟨Vec.fromList [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], rfl⟩

/-- Serialize structural fields; unsupported or inconsistent values remain
representable and must pass the selected profile before loading. -/
def writeHeader64 (header : Header64) : Std.Logical.ByteArray :=
  writeExact header.ident ++
    writeLittleEndian (count := 2) header.objectType ++
    writeLittleEndian (count := 2) header.machine ++
    writeLittleEndian (count := 4) header.version ++
    writeLittleEndian (count := 8) header.entry ++
    writeLittleEndian (count := 8) header.programOffset ++
    writeLittleEndian (count := 8) header.sectionOffset ++
    writeLittleEndian (count := 4) header.flags ++
    writeLittleEndian (count := 2) header.headerSize ++
    writeLittleEndian (count := 2) header.programEntrySize ++
    writeLittleEndian (count := 2) header.programCount ++
    writeLittleEndian (count := 2) header.sectionEntrySize ++
    writeLittleEndian (count := 2) header.sectionCount ++
    writeLittleEndian (count := 2) header.stringSectionIndex

/-- Read all fields under an explicitly selected ELF64 little-endian layout.
This raw field decoder deliberately does not classify other ELF layouts. -/
def readHeader64Fields (input : Std.Logical.ByteArray) : ParseResult Header64 :=
  continueRead (takeExactSized 16 input) fun ident input =>
  continueRead (takeLittleEndian 2 input) fun objectType input =>
  continueRead (takeLittleEndian 2 input) fun machine input =>
  continueRead (takeLittleEndian 4 input) fun version input =>
  continueRead (takeLittleEndian 8 input) fun entry input =>
  continueRead (takeLittleEndian 8 input) fun programOffset input =>
  continueRead (takeLittleEndian 8 input) fun sectionOffset input =>
  continueRead (takeLittleEndian 4 input) fun flags input =>
  continueRead (takeLittleEndian 2 input) fun headerSize input =>
  continueRead (takeLittleEndian 2 input) fun programEntrySize input =>
  continueRead (takeLittleEndian 2 input) fun programCount input =>
  continueRead (takeLittleEndian 2 input) fun sectionEntrySize input =>
  continueRead (takeLittleEndian 2 input) fun sectionCount input =>
  continueRead (takeLittleEndian 2 input) fun stringSectionIndex input =>
  .done { ident, objectType, machine, version, entry, programOffset, sectionOffset, flags, headerSize, programEntrySize, programCount, sectionEntrySize, sectionCount, stringSectionIndex } input

@[simp] theorem writeHeader64_length (header : Header64) :
    (writeHeader64 header).length = 64 := by
  simp [writeHeader64, writeExact]

/-- Full field recovery with the identical trailing bytes. -/
theorem readHeader64Fields_write_append (header : Header64)
    (suffix : Std.Logical.ByteArray) :
    readHeader64Fields (writeHeader64 header ++ suffix) = .done header suffix := by
  simp [readHeader64Fields, writeHeader64, Vec.append_assoc, continueRead]

/-- A successful raw field read consumes exactly one serialized ELF header. -/
theorem readHeader64Fields_done {input rest : Std.Logical.ByteArray} {header : Header64}
    (success : readHeader64Fields input = .done header rest) :
    input = writeHeader64 header ++ rest := by
  unfold readHeader64Fields continueRead at success
  cases identResult : takeExactSized 16 input <;> simp [identResult] at success
  case done ident rest0 =>
    cases objectTypeResult : takeLittleEndian 2 rest0 <;>
      simp [objectTypeResult] at success
    case done objectType rest1 =>
      cases machineResult : takeLittleEndian 2 rest1 <;>
        simp [machineResult] at success
      case done machine rest2 =>
        cases versionResult : takeLittleEndian 4 rest2 <;>
          simp [versionResult] at success
        case done version rest3 =>
          cases entryResult : takeLittleEndian 8 rest3 <;>
            simp [entryResult] at success
          case done entry rest4 =>
            cases programOffsetResult : takeLittleEndian 8 rest4 <;>
              simp [programOffsetResult] at success
            case done programOffset rest5 =>
              cases sectionOffsetResult : takeLittleEndian 8 rest5 <;>
                simp [sectionOffsetResult] at success
              case done sectionOffset rest6 =>
                cases flagsResult : takeLittleEndian 4 rest6 <;>
                  simp [flagsResult] at success
                case done flags rest7 =>
                  cases headerSizeResult : takeLittleEndian 2 rest7 <;>
                    simp [headerSizeResult] at success
                  case done headerSize rest8 =>
                    cases programEntrySizeResult : takeLittleEndian 2 rest8 <;>
                      simp [programEntrySizeResult] at success
                    case done programEntrySize rest9 =>
                      cases programCountResult : takeLittleEndian 2 rest9 <;>
                        simp [programCountResult] at success
                      case done programCount rest10 =>
                        cases sectionEntrySizeResult : takeLittleEndian 2 rest10 <;>
                          simp [sectionEntrySizeResult] at success
                        case done sectionEntrySize rest11 =>
                          cases sectionCountResult : takeLittleEndian 2 rest11 <;>
                            simp [sectionCountResult] at success
                          case done sectionCount rest12 =>
                            cases stringSectionIndexResult : takeLittleEndian 2 rest12 <;>
                              simp [stringSectionIndexResult] at success
                            case done stringSectionIndex rest13 =>
                              rcases success with ⟨headerEq, restEq⟩
                              subst header
                              subst rest
                              have identConsumed := takeExactSized_done identResult
                              have objectTypeConsumed := takeLittleEndian_done objectTypeResult
                              have machineConsumed := takeLittleEndian_done machineResult
                              have versionConsumed := takeLittleEndian_done versionResult
                              have entryConsumed := takeLittleEndian_done entryResult
                              have programOffsetConsumed := takeLittleEndian_done programOffsetResult
                              have sectionOffsetConsumed := takeLittleEndian_done sectionOffsetResult
                              have flagsConsumed := takeLittleEndian_done flagsResult
                              have headerSizeConsumed := takeLittleEndian_done headerSizeResult
                              have programEntrySizeConsumed :=
                                takeLittleEndian_done programEntrySizeResult
                              have programCountConsumed := takeLittleEndian_done programCountResult
                              have sectionEntrySizeConsumed :=
                                takeLittleEndian_done sectionEntrySizeResult
                              have sectionCountConsumed := takeLittleEndian_done sectionCountResult
                              have stringSectionIndexConsumed :=
                                takeLittleEndian_done stringSectionIndexResult
                              rw [identConsumed, objectTypeConsumed, machineConsumed,
                                versionConsumed, entryConsumed, programOffsetConsumed,
                                sectionOffsetConsumed, flagsConsumed, headerSizeConsumed,
                                programEntrySizeConsumed, programCountConsumed,
                                sectionEntrySizeConsumed, sectionCountConsumed,
                                stringSectionIndexConsumed]
                              simp [writeHeader64, Vec.append_assoc]

/-- A successful raw field read advances by exactly the ELF64 header width. -/
theorem readHeader64Fields_consumes64 {input rest : Std.Logical.ByteArray} {header : Header64}
    (success : readHeader64Fields input = .done header rest) :
    input.length = 64 + rest.length := by
  rw [readHeader64Fields_done success]
  simp

/-- Bounded canonical identification profile, not a loader admissibility test.
Other OSABI values and padding are retained by the raw decoder but outside
this selected subset. -/
def Header64.Canonical (header : Header64) : Prop :=
  header.ident = ident64LE ∧ header.version = 1 ∧ header.headerSize = 64

instance (header : Header64) : Decidable header.Canonical :=
  inferInstanceAs (Decidable (header.ident = ident64LE ∧
    header.version = 1 ∧ header.headerSize = 64))

/-- Check every available byte in the selected fixed fields. A truncated
header with an already incompatible fixed byte has no canonical completion. -/
def compatibleHeaderPrefix (input : Std.Logical.ByteArray) : Bool :=
  decide (input.take 16 = ident64LE.1.take input.length) &&
  decide ((input.drop 20).take 4 =
    (writeLittleEndian (count := 4) (1 : BitVec 32)).take (input.length - 20)) &&
  decide ((input.drop 52).take 2 =
    (writeLittleEndian (count := 2) (64 : BitVec 16)).take (input.length - 52))

/-- Select the bounded canonical subset. Incomplete input is repairable only
while its already present constrained bytes agree with the selected profile. -/
def readHeader64 (input : Std.Logical.ByteArray) : ParseResult Header64 :=
  match readHeader64Fields input with
  | .done header rest =>
    if header.Canonical then .done header rest
    else .invalid (.unsupported "ELF64 little-endian canonical header profile")
  | .needMore _ =>
    if compatibleHeaderPrefix input then .needMore (some (64 - input.length))
    else .invalid (.unsupported "ELF64 little-endian canonical header prefix")
  | .invalid error => .invalid error

theorem readHeader64_write_append (header : Header64)
    (canonical : header.Canonical) (suffix : Std.Logical.ByteArray) :
    readHeader64 (writeHeader64 header ++ suffix) = .done header suffix := by
  simp [readHeader64, readHeader64Fields_write_append, canonical]

/-- Successful selected parsing retains the checked profile, not loadability. -/
theorem readHeader64_canonical {input rest : Std.Logical.ByteArray} {header : Header64}
    (success : readHeader64 input = .done header rest) : header.Canonical := by
  unfold readHeader64 at success
  cases parsed : readHeader64Fields input <;> simp only [parsed] at success
  case done value suffix =>
    split at success
    next accepted => cases success; exact accepted
    next rejected => contradiction
  case needMore hint => split at success <;> contradiction
  case invalid error => contradiction

/-- Successful selected parsing consumes the raw header representation exactly. -/
theorem readHeader64_done {input rest : Std.Logical.ByteArray} {header : Header64}
    (success : readHeader64 input = .done header rest) :
    input = writeHeader64 header ++ rest := by
  unfold readHeader64 at success
  cases parsed : readHeader64Fields input <;> simp only [parsed] at success
  case done value suffix =>
    split at success
    next accepted =>
      injection success with headerEq restEq
      subst header
      subst rest
      exact readHeader64Fields_done parsed
    next rejected => contradiction
  case needMore hint => split at success <;> contradiction
  case invalid error => contradiction

/-- Successful selected parsing advances by exactly the ELF64 header width. -/
theorem readHeader64_consumes64 {input rest : Std.Logical.ByteArray} {header : Header64}
    (success : readHeader64 input = .done header rest) :
    input.length = 64 + rest.length := by
  rw [readHeader64_done success]
  simp

end Grass.Artifact.ELF
