import Grass.Construct.Link.Raw
import Grass.Unsafe.EmitProgram

/-!
# Checked raw-emission source-map projection

`checkLinkSourceMap` validates consecutive offsets and positive byte lengths
before projecting a `RawProgramEmission` into construction-owned
`Link.SourceMapEntry` values. Accepted entries retain exact block and
`SourceOrigin` data. Checked theorems prove every range fits inside the emitted
byte stream and every emitted byte belongs to one range. No artifact layout or
byte-semantics certificate is created.
-/

namespace Grass.Unsafe

open Grass.Construct.Link Grass.Construct.Source

universe u v w

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}

/-- Consecutive positive-width invariant required by link source-map entries. -/
def LinkMapReadyFrom :
    Nat → List (RawProgramEncodedInstruction Instruction) → Prop
  | _, [] => True
  | expected, item :: rest =>
      item.offset = expected ∧ 0 < item.bytes.length ∧
        LinkMapReadyFrom item.endOffset rest

/-- Consecutive positive source ranges in one exact section. -/
def SourceMapConsecutiveFrom (sectionId : SectionId) :
    Nat → List SourceMapEntry → Prop
  | _, [] => True
  | expected, entry :: rest =>
      entry.sectionId = sectionId ∧ entry.offset = expected ∧
        0 < entry.length ∧
        SourceMapConsecutiveFrom sectionId
          (entry.offset + entry.length) rest

/-- `LinkSourceMapError` records the first structural reason raw items cannot
become positive consecutive link source ranges. -/
inductive LinkSourceMapError where
  | offsetMismatch (block : Grass.CFG.BlockId)
      (origin : Grass.Construct.Fragment.SourceOrigin)
      (expected actual : Nat)
  | zeroWidth (block : Grass.CFG.BlockId)
      (origin : Grass.Construct.Fragment.SourceOrigin) (offset : Nat)
deriving Repr, DecidableEq

private def firstLinkSourceMapError :
    Nat → List (RawProgramEncodedInstruction Instruction) →
      Option LinkSourceMapError
  | _, [] => none
  | expected, item :: rest =>
      if item.offset = expected then
        if 0 < item.bytes.length then
          firstLinkSourceMapError item.endOffset rest
        else
          some (.zeroWidth item.lowered.block item.lowered.origin item.offset)
      else
        some (.offsetMismatch item.lowered.block item.lowered.origin
          expected item.offset)

private theorem firstLinkSourceMapError_eq_none_ready
    (expected : Nat) (items : List (RawProgramEncodedInstruction Instruction))
    (h : firstLinkSourceMapError expected items = none) :
    LinkMapReadyFrom expected items := by
  induction items generalizing expected with
  | nil => trivial
  | cons head rest ih =>
      simp only [firstLinkSourceMapError] at h
      split at h
      next offsetExact =>
        split at h
        next positive => exact ⟨offsetExact, positive, ih head.endOffset h⟩
        next notPositive => contradiction
      next offsetMismatch => contradiction

private theorem linkMapReady_positive
    (expected : Nat) (items : List (RawProgramEncodedInstruction Instruction))
    (ready : LinkMapReadyFrom expected items) :
    ∀ item ∈ items, 0 < item.bytes.length := by
  induction items generalizing expected with
  | nil => simp
  | cons head rest ih =>
      rcases ready with ⟨offsetExact, positive, restReady⟩
      intro item hitem
      simp only [List.mem_cons] at hitem
      rcases hitem with rfl | hitem
      · exact positive
      · exact ih head.endOffset restReady item hitem

private theorem linkMapReady_bounded
    (expected : Nat) (items : List (RawProgramEncodedInstruction Instruction))
    (ready : LinkMapReadyFrom expected items) :
    ∀ item ∈ items,
      item.offset + item.bytes.length ≤
        expected + (items.flatMap RawProgramEncodedInstruction.bytes).length := by
  induction items generalizing expected with
  | nil => simp
  | cons head rest ih =>
      rcases ready with ⟨offsetExact, positive, restReady⟩
      intro item hitem
      simp only [List.mem_cons] at hitem
      rcases hitem with rfl | hitem
      · simp only [List.flatMap_cons, List.length_append]
        omega
      · have bound := ih head.endOffset restReady item hitem
        simp only [List.flatMap_cons, List.length_append]
        unfold RawProgramEncodedInstruction.endOffset at bound
        omega

private theorem linkMapReady_coversByte
    (expected : Nat) (items : List (RawProgramEncodedInstruction Instruction))
    (ready : LinkMapReadyFrom expected items)
    (offset : Nat) (offsetLower : expected ≤ offset)
    (offsetUpper :
      offset < expected +
        (items.flatMap RawProgramEncodedInstruction.bytes).length) :
    ∃ item ∈ items,
      item.offset ≤ offset ∧ offset < item.offset + item.bytes.length := by
  induction items generalizing expected with
  | nil =>
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero] at offsetUpper
      omega
  | cons head rest ih =>
      rcases ready with ⟨offsetExact, positive, restReady⟩
      by_cases inHead : offset < head.offset + head.bytes.length
      · exact ⟨head, by simp, by omega, inHead⟩
      · have restUpper :
            offset < head.endOffset +
              (rest.flatMap RawProgramEncodedInstruction.bytes).length := by
          simp only [List.flatMap_cons, List.length_append] at offsetUpper
          simp only [RawProgramEncodedInstruction.endOffset]
          omega
        obtain ⟨item, hitem, lower, upper⟩ :=
          ih head.endOffset restReady (by
            simp only [RawProgramEncodedInstruction.endOffset]
            omega) restUpper
        exact ⟨item, by simp [hitem], lower, upper⟩

private theorem linkMapReady_sourceMapConsecutive
    (sectionId : SectionId) (expected : Nat)
    (items : List (RawProgramEncodedInstruction Instruction))
    (ready : LinkMapReadyFrom expected items) :
    SourceMapConsecutiveFrom sectionId expected
      (items.map fun item =>
        ⟨sectionId, item.offset, item.bytes.length,
          item.lowered.block, item.lowered.origin⟩) := by
  induction items generalizing expected with
  | nil => trivial
  | cons head rest ih =>
      rcases ready with ⟨offsetExact, positive, restReady⟩
      refine ⟨rfl, offsetExact, positive, ?_⟩
      simpa [RawProgramEncodedInstruction.endOffset] using
        ih head.endOffset restReady

private theorem sourceMapConsecutive_offsetsAtLeast
    (sectionId : SectionId) (expected : Nat) (entries : List SourceMapEntry)
    (ready : SourceMapConsecutiveFrom sectionId expected entries) :
    ∀ entry ∈ entries, expected ≤ entry.offset := by
  induction entries generalizing expected with
  | nil => simp
  | cons head rest ih =>
      rcases ready with ⟨sectionExact, offsetExact, positive, restReady⟩
      intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · omega
      · have later := ih (head.offset + head.length) restReady entry hentry
        omega

private theorem sourceMapConsecutive_pairwise
    (sectionId : SectionId) (expected : Nat) (entries : List SourceMapEntry)
    (ready : SourceMapConsecutiveFrom sectionId expected entries) :
    entries.Pairwise
      (fun left right => left.offset + left.length ≤ right.offset) := by
  induction entries generalizing expected with
  | nil => exact List.Pairwise.nil
  | cons head rest ih =>
      rcases ready with ⟨sectionExact, offsetExact, positive, restReady⟩
      exact List.Pairwise.cons
        (fun right hright =>
          sourceMapConsecutive_offsetsAtLeast sectionId
            (head.offset + head.length) rest restReady right hright)
        (ih (head.offset + head.length) restReady)

namespace RawProgramEmission

/-- Link source-map entries in exact emitted-item order. -/
def linkSourceMap (emission : RawProgramEmission State Terminal Instruction)
    (sectionId : SectionId) : List SourceMapEntry :=
  emission.items.map fun item =>
    ⟨sectionId, item.offset, item.bytes.length,
      item.lowered.block, item.lowered.origin⟩

end RawProgramEmission

/-- Raw emission proven suitable for positive-length link source-map ranges. -/
structure CheckedLinkSourceMap
    (emission : RawProgramEmission State Terminal Instruction)
    (sectionId : SectionId) : Type (max u v w) where
  ready : LinkMapReadyFrom 0 emission.items

namespace CheckedLinkSourceMap

/-- Exact checked source-map projection. -/
def entries
    {emission : RawProgramEmission State Terminal Instruction}
    {sectionId : SectionId}
    (_checked : CheckedLinkSourceMap emission sectionId) :
    List SourceMapEntry :=
  emission.linkSourceMap sectionId

/-- Every projected entry names the section selected for this source map. -/
theorem entrySectionExact
    {emission : RawProgramEmission State Terminal Instruction}
    {sectionId : SectionId}
    (checked : CheckedLinkSourceMap emission sectionId)
    (entry : SourceMapEntry) (hentry : entry ∈ checked.entries) :
    entry.sectionId = sectionId := by
  simp only [entries, RawProgramEmission.linkSourceMap, List.mem_map] at hentry
  obtain ⟨item, hitem, rfl⟩ := hentry
  rfl

/-- Checked entries form one exact consecutive positive range sequence. -/
theorem entriesConsecutive
    {emission : RawProgramEmission State Terminal Instruction}
    {sectionId : SectionId}
    (checked : CheckedLinkSourceMap emission sectionId) :
    SourceMapConsecutiveFrom sectionId 0 checked.entries :=
  linkMapReady_sourceMapConsecutive sectionId 0 emission.items checked.ready

/-- Earlier checked source ranges end no later than every subsequent range. -/
theorem entriesOrderedNonoverlap
    {emission : RawProgramEmission State Terminal Instruction}
    {sectionId : SectionId}
    (checked : CheckedLinkSourceMap emission sectionId) :
    checked.entries.Pairwise
      (fun left right => left.offset + left.length ≤ right.offset) :=
  sourceMapConsecutive_pairwise sectionId 0 checked.entries
    checked.entriesConsecutive

/-- Every checked link source-map entry has positive length. -/
theorem entryPositive
    {emission : RawProgramEmission State Terminal Instruction}
    {sectionId : SectionId}
    (checked : CheckedLinkSourceMap emission sectionId)
    (entry : SourceMapEntry) (hentry : entry ∈ checked.entries) :
    0 < entry.length := by
  simp only [entries, RawProgramEmission.linkSourceMap, List.mem_map] at hentry
  obtain ⟨item, hitem, rfl⟩ := hentry
  exact linkMapReady_positive 0 emission.items checked.ready item hitem

/-- Every checked link source-map range fits inside the emitted byte stream. -/
theorem entryBounded
    {emission : RawProgramEmission State Terminal Instruction}
    {sectionId : SectionId}
    (checked : CheckedLinkSourceMap emission sectionId)
    (entry : SourceMapEntry) (hentry : entry ∈ checked.entries) :
    entry.offset + entry.length ≤ emission.byteLength := by
  simp only [entries, RawProgramEmission.linkSourceMap, List.mem_map] at hentry
  obtain ⟨item, hitem, rfl⟩ := hentry
  simpa [RawProgramEmission.byteLength, RawProgramEmission.bytes] using
    linkMapReady_bounded 0 emission.items checked.ready item hitem

/-- The checked source ranges account for exactly the emitted byte length. -/
theorem entriesLengthSumExact
    {emission : RawProgramEmission State Terminal Instruction}
    {sectionId : SectionId}
    (checked : CheckedLinkSourceMap emission sectionId) :
    (checked.entries.map SourceMapEntry.length).sum = emission.byteLength := by
  simp only [entries, RawProgramEmission.linkSourceMap,
    RawProgramEmission.byteLength, RawProgramEmission.bytes, List.map_map]
  change (emission.items.map fun item => item.bytes.length).sum =
    (emission.items.flatMap RawProgramEncodedInstruction.bytes).length
  induction emission.items with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.length_append]
      omega

/-- Every emitted byte offset belongs to a checked source-map range. -/
theorem entryForByte
    {emission : RawProgramEmission State Terminal Instruction}
    {sectionId : SectionId}
    (checked : CheckedLinkSourceMap emission sectionId)
    (offset : Nat) (hbound : offset < emission.byteLength) :
    ∃ entry ∈ checked.entries,
      entry.offset ≤ offset ∧ offset < entry.offset + entry.length := by
  have upper :
      offset < 0 +
        (emission.items.flatMap RawProgramEncodedInstruction.bytes).length := by
    simpa [RawProgramEmission.byteLength, RawProgramEmission.bytes] using hbound
  obtain ⟨item, hitem, lower, upper⟩ :=
    linkMapReady_coversByte 0 emission.items checked.ready offset
      (Nat.zero_le offset) upper
  refine ⟨⟨sectionId, item.offset, item.bytes.length,
    item.lowered.block, item.lowered.origin⟩, ?_, lower, upper⟩
  exact List.mem_map.mpr ⟨item, hitem, rfl⟩

end CheckedLinkSourceMap

/-- Validate raw program items before projecting positive link source ranges. -/
def checkLinkSourceMap
    (emission : RawProgramEmission State Terminal Instruction)
    (sectionId : SectionId) :
    Except LinkSourceMapError (CheckedLinkSourceMap emission sectionId) :=
  match h : firstLinkSourceMapError 0 emission.items with
  | some error => .error error
  | none => .ok ⟨firstLinkSourceMapError_eq_none_ready 0 emission.items h⟩

end Grass.Unsafe
