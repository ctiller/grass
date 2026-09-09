import Grass.Artifact.PE.Validation

/-! # PE placement invariance under same-length payload replacement -/

namespace Grass.Artifact.PE

open Grass.Std.Logical

/-- Coordinates observable by a source/relocation consumer. -/
def placementSpans (placed : List PlacedSection) : List (FileSpan × FileSpan) :=
  placed.map fun item => (item.virtualSpan, item.rawSpan)

/-- Payload lengths in source section order. -/
def sectionContentLengths (sections : List RawSection) : List Nat :=
  sections.map fun source => source.contents.length

/-- `placementSpans_placeSectionsFrom_eq_of_lengths_eq` proves every virtual
and raw span equal under equal payload lengths, even when names or flags differ. -/
theorem placementSpans_placeSectionsFrom_eq_of_lengths_eq
    (virtualCursor rawCursor sectionAlignment fileAlignment : Nat)
    {left right : List RawSection}
    (lengths : sectionContentLengths left = sectionContentLengths right) :
    placementSpans
        (placeSectionsFrom virtualCursor rawCursor sectionAlignment fileAlignment left) =
      placementSpans
        (placeSectionsFrom virtualCursor rawCursor sectionAlignment fileAlignment right) := by
  induction left generalizing right virtualCursor rawCursor with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp [sectionContentLengths] at lengths
  | cons leftHead leftTail ih =>
      cases right with
      | nil => simp [sectionContentLengths] at lengths
      | cons rightHead rightTail =>
          simp only [sectionContentLengths, List.map_cons, List.cons.injEq] at lengths
          rcases lengths with ⟨headLength, tailLengths⟩
          simp only [placeSectionsFrom, placementSpans, List.map_cons,
            FileSpan.endOffset]
          have virtualEnd :
              (alignUp virtualCursor sectionAlignment + leftHead.contents.length) =
                (alignUp virtualCursor sectionAlignment + rightHead.contents.length) := by
            omega
          have rawSize :
              alignUp leftHead.contents.length fileAlignment =
                alignUp rightHead.contents.length fileAlignment := by
            rw [headLength]
          congr 1
          · simp [headLength]
          · rw [headLength]
            change placementSpans (placeSectionsFrom _ _ _ _ leftTail) =
              placementSpans (placeSectionsFrom _ _ _ _ rightTail)
            exact ih tailLengths
              (virtualCursor := alignUp virtualCursor sectionAlignment +
                rightHead.contents.length)
              (rawCursor := alignUp rawCursor fileAlignment +
                alignUp rightHead.contents.length fileAlignment)

/-- Corresponding placed sections with equal payload lengths and virtual bases
resolve the same section-relative location. This is the pointwise bridge used
after applying placement span invariance. -/
theorem resolveSectionLocation?_eq_of_selected
    {left right : Vec PlacedSection} (location : SectionLocation)
    {leftPlaced rightPlaced : PlacedSection}
    (leftSelected : left.get? location.sectionIndex = some leftPlaced)
    (rightSelected : right.get? location.sectionIndex = some rightPlaced)
    (lengthEq : leftPlaced.source.contents.length =
      rightPlaced.source.contents.length)
    (startEq : leftPlaced.virtualSpan.start = rightPlaced.virtualSpan.start) :
    resolveSectionLocation? left location = resolveSectionLocation? right location := by
  simp only [resolveSectionLocation?, leftSelected, rightSelected]
  dsimp
  split <;> rename_i leftBound
  · rw [if_pos (by omega : location.offset < rightPlaced.source.contents.length)]
    simp [startEq]
  · rw [if_neg (by omega : ¬ location.offset < rightPlaced.source.contents.length)]

/-- Complete image placement has identical coordinates when requested payloads
have the same lengths in the same order. -/
theorem placementSpans_placeImageSections_eq_of_lengths_eq
    {left right : ExecutableImageDescription}
    (lengths : sectionContentLengths left.sections.toList =
      sectionContentLengths right.sections.toList) :
    placementSpans (placeImageSections left).toList =
      placementSpans (placeImageSections right).toList := by
  have countEq : left.sections.length = right.sections.length := by
    have mappedLength := congrArg List.length lengths
    simp only [sectionContentLengths, List.length_map] at mappedLength
    change left.sections.toList.length = right.sections.toList.length
    exact mappedLength
  unfold placeImageSections
  simp only
  rw [countEq]
  exact placementSpans_placeSectionsFrom_eq_of_lengths_eq _ _ _ _ lengths

/-- Equal global span projections make section-relative resolution invariant,
provided each placement's virtual size remains its source payload length. The
corresponding selected records are recovered internally from the common index. -/
theorem resolveSectionLocation?_eq_of_placementSpans_eq
    {left right : Vec PlacedSection} (location : SectionLocation)
    (spans : placementSpans left.toList = placementSpans right.toList)
    (leftSizes : ∀ item ∈ left.toList,
      item.source.contents.length = item.virtualSpan.size)
    (rightSizes : ∀ item ∈ right.toList,
      item.source.contents.length = item.virtualSpan.size) :
    resolveSectionLocation? left location = resolveSectionLocation? right location := by
  have countEq : left.length = right.length := by
    have mappedLength := congrArg List.length spans
    simp only [placementSpans, List.length_map] at mappedLength
    change left.toList.length = right.toList.length
    exact mappedLength
  by_cases inBounds : location.sectionIndex < left.length
  · let leftPlaced := left.get location.sectionIndex inBounds
    have rightInBounds : location.sectionIndex < right.length := by omega
    let rightPlaced := right.get location.sectionIndex rightInBounds
    have leftSelected : left.get? location.sectionIndex = some leftPlaced :=
      Vec.get?_eq_some_get left location.sectionIndex inBounds
    have rightSelected : right.get? location.sectionIndex = some rightPlaced :=
      Vec.get?_eq_some_get right location.sectionIndex rightInBounds
    have selectedSpans := congrArg (fun entries => entries[location.sectionIndex]?) spans
    have spanEq :
        (leftPlaced.virtualSpan, leftPlaced.rawSpan) =
          (rightPlaced.virtualSpan, rightPlaced.rawSpan) := by
      have leftListSelected : left.toList[location.sectionIndex]? = some leftPlaced :=
        leftSelected
      have rightListSelected : right.toList[location.sectionIndex]? = some rightPlaced :=
        rightSelected
      simpa [placementSpans, leftListSelected, rightListSelected] using selectedSpans
    have leftMember : leftPlaced ∈ left.toList :=
      (Vec.mem_iff_exists_get?).mpr ⟨location.sectionIndex, leftSelected⟩
    have rightMember : rightPlaced ∈ right.toList :=
      (Vec.mem_iff_exists_get?).mpr ⟨location.sectionIndex, rightSelected⟩
    apply resolveSectionLocation?_eq_of_selected location leftSelected rightSelected
    · rw [leftSizes leftPlaced leftMember, rightSizes rightPlaced rightMember]
      exact congrArg (fun pair => pair.1.size) spanEq
    · exact congrArg (fun pair => pair.1.start) spanEq
  · have leftNone := Vec.get?_eq_none left (Nat.le_of_not_gt inBounds)
    have rightBound : right.length ≤ location.sectionIndex := by omega
    have rightNone := Vec.get?_eq_none right rightBound
    simp [resolveSectionLocation?, leftNone, rightNone]

end Grass.Artifact.PE
