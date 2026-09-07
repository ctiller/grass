import Grass.Construct.Link.Raw
import Grass.Unsafe.EmitProgram

/-!
# Checked raw-emission source-map projection

`checkLinkSourceMap` validates consecutive offsets and positive byte lengths
before projecting a `RawProgramEmission` into construction-owned
`Link.SourceMapEntry` values. Accepted entries retain exact block and
`SourceOrigin` data, and `CheckedLinkSourceMap.entryBounded` proves every range
fits inside the emitted byte stream. No artifact layout or byte-semantics
certificate is created.
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
