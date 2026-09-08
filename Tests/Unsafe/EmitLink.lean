import Grass.Unsafe.EmitLink

/-!
# Checked raw-emission link source-map fixtures

Fixtures accept consecutive positive encodings and reject zero-width or
mis-offset items with exact block/origin diagnostics.
-/

namespace Grass.Tests.Unsafe.EmitLink

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Link
  Grass.Construct.Source Grass.Unsafe

private structure Instruction where
  payload : List UInt8
deriving Repr, DecidableEq

private def blockId (name : String) : BlockId :=
  ⟨⟨"test.unsafe.emit-link", name⟩⟩
private def sectionId : SectionId :=
  ⟨⟨"test.unsafe.emit-link", "text"⟩⟩
private def first : Instruction := ⟨[0x10, 0x11]⟩
private def second : Instruction := ⟨[0x20]⟩
private def empty : Instruction := ⟨[]⟩
private def encoder : RawEncoder Instruction := ⟨Instruction.payload⟩
private def taint : Taint := ⟨.externalGenerator, "unverified bytes"⟩
private def graph : Graph Unit Unit := ⟨blockId "entry", []⟩

private def lowered (index : Nat) (instruction : Instruction) :
    LoweredInstruction Instruction :=
  ⟨blockId "entry", ⟨[], [], index⟩, instruction⟩

private def program (instructions : List Instruction) :
    LoweredProgram Unit Unit Instruction where
  graph := graph
  items := match instructions with
    | [first, second] => [lowered 0 first, lowered 1 second]
    | _ => []

private def accepted : RawProgramEmission Unit Unit Instruction :=
  emitRawProgram (program [first, second]) encoder taint

example : (checkLinkSourceMap accepted sectionId).isOk = true := rfl

private def checked : CheckedLinkSourceMap accepted sectionId :=
  ⟨by
    change (0 = 0 ∧ 0 < 2 ∧ (2 = 2 ∧ 0 < 1 ∧ True))
    decide⟩

example : checked.entries = [
    ⟨sectionId, 0, 2, blockId "entry", ⟨[], [], 0⟩⟩,
    ⟨sectionId, 2, 1, blockId "entry", ⟨[], [], 1⟩⟩] := rfl

example : SourceMapConsecutiveFrom sectionId 0 checked.entries :=
  checked.entriesConsecutive
example : checked.entries.Pairwise
    (fun left right => left.offset + left.length ≤ right.offset) :=
  checked.entriesOrderedNonoverlap

example (entry : SourceMapEntry) (hentry : entry ∈ checked.entries) :
    0 < entry.length := checked.entryPositive entry hentry
example (entry : SourceMapEntry) (hentry : entry ∈ checked.entries) :
    entry.offset + entry.length ≤ accepted.byteLength :=
  checked.entryBounded entry hentry
example : (checked.entries.map SourceMapEntry.length).sum =
    accepted.byteLength :=
  checked.entriesLengthSumExact
example (offset : Nat) (hbound : offset < accepted.byteLength) :
    ∃ entry ∈ checked.entries,
      entry.offset ≤ offset ∧ offset < entry.offset + entry.length :=
  checked.entryForByte offset hbound
example (offset : Nat) (hbound : offset < accepted.byteLength) :
    ∃ entry : SourceMapEntry,
      (entry ∈ checked.entries ∧ entry.offset ≤ offset ∧
        offset < entry.offset + entry.length) ∧
      ∀ other : SourceMapEntry,
        other ∈ checked.entries ∧ other.offset ≤ offset ∧
          offset < other.offset + other.length → other = entry :=
  checked.uniqueEntryForByte offset hbound
example (offset : Nat) (left right : SourceMapEntry)
    (leftMem : left ∈ checked.entries)
    (rightMem : right ∈ checked.entries)
    (leftLower : left.offset ≤ offset)
    (leftUpper : offset < left.offset + left.length)
    (rightLower : right.offset ≤ offset)
    (rightUpper : offset < right.offset + right.length) :
    left = right :=
  checked.entryContainingByteUnique offset left right leftMem rightMem
    leftLower leftUpper rightLower rightUpper

private def zeroWidth : RawProgramEmission Unit Unit Instruction :=
  emitRawProgram (program [first, empty]) encoder taint

example : checkLinkSourceMap zeroWidth sectionId =
    .error (.zeroWidth (blockId "entry") ⟨[], [], 1⟩ 2) := rfl

private def misoffset : RawProgramEmission Unit Unit Instruction :=
  { accepted with items := [
      ⟨lowered 0 first, 0, first.payload⟩,
      ⟨lowered 1 second, 9, second.payload⟩] }

example : checkLinkSourceMap misoffset sectionId =
    .error (.offsetMismatch (blockId "entry") ⟨[], [], 1⟩ 2 9) := rfl

end Grass.Tests.Unsafe.EmitLink
