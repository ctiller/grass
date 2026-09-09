import Grass.Artifact.PE.LayoutInvariance

/-! # Coordinate transport between independently checked image layouts

Prototype and final bytes stay in their own plans. Equal payload lengths,
imports and entry locations suffice to relate their coordinates; preparation
success and source instruction correctness are separate obligations.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical

/-- The source lengths that determine section placement. -/
def sectionSizes (description : ExecutableImageDescription) : Vec Nat :=
  description.sections.map (fun source => source.contents.length)

/-- Import rebasing changes addresses but not the added section's size. -/
theorem sectionSizes_materializeImports (description : ExecutableImageDescription) :
    sectionSizes (materializeImports description) =
      if description.imports.length = 0 then sectionSizes description
      else sectionSizes description ++
        Vec.singleton (writeImportSection 0 description.imports).length := by
  unfold materializeImports
  split
  · rfl
  · unfold sectionSizes
    change (description.sections ++ Vec.fromList [makeImportSection _ description.imports]).map
      (fun source => source.contents.length) = _
    rw [Vec.map_append]
    congr 1
    change Vec.singleton (writeImportSection _ description.imports).length = _
    rw [length_writeImportSection_independent_rva _ 0]

/-- Equal source section lengths and identical imports yield equal materialized lengths. -/
theorem sectionSizes_materializeImports_eq
    (left right : ExecutableImageDescription)
    (sizes : sectionSizes left = sectionSizes right)
    (imports : left.imports = right.imports) :
    sectionSizes (materializeImports left) = sectionSizes (materializeImports right) := by
  rw [sectionSizes_materializeImports, sectionSizes_materializeImports, sizes, imports]

/-- Equal mapped spans determine the same maximum exclusive end. -/
theorem greatestVirtualEnd_eq_of_spans_eq (left right : List PlacedSection)
    (spans : left.map (fun s => (s.virtualSpan, s.rawSpan)) =
      right.map (fun s => (s.virtualSpan, s.rawSpan))) :
    greatestVirtualEnd left = greatestVirtualEnd right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all [greatestVirtualEnd]
  | cons head tail ih =>
      cases right with
      | nil => simp at spans
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at spans
          simp only [greatestVirtualEnd]
          rw [spans.1.1, ih rest spans.2]

/-- Equal mapped spans determine the same last section RVA. -/
theorem lastVirtualStart_eq_of_spans_eq (left right : List PlacedSection)
    (spans : left.map (fun s => (s.virtualSpan, s.rawSpan)) =
      right.map (fun s => (s.virtualSpan, s.rawSpan))) :
    lastVirtualStart left = lastVirtualStart right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all [lastVirtualStart]
  | cons head tail ih =>
      cases right with
      | nil => simp at spans
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at spans
          cases tail with
          | nil =>
              cases rest <;> simp_all [lastVirtualStart]
          | cons tailHead tailRest =>
              cases rest with
              | nil => simp at spans
              | cons otherHead otherRest =>
                  exact ih (otherHead :: otherRest) spans.2

/-- Requested payload lengths and import requests determine all final spans. -/
theorem ImageLayout.placementSpans_eq_of_lengths_eq (left right : ImageLayout)
    (sizes : sectionSizes left.requested = sectionSizes right.requested)
    (imports : left.requested.imports = right.requested.imports) :
    placementSpans left.placed.toList = placementSpans right.placed.toList := by
  rw [left.placed_eq, right.placed_eq, left.materialized_eq, right.materialized_eq]
  apply placementSpans_placeImageSections_eq_of_lengths_eq
  exact congrArg Vec.toList (sectionSizes_materializeImports_eq _ _ sizes imports)

/-- Every proof-linked layout retains source lengths as virtual extents. -/
theorem ImageLayout.sourceLengths_eq_virtualSizes (layout : ImageLayout)
    (placedSection : PlacedSection) (member : placedSection ∈ layout.placed.toList) :
    placedSection.source.contents.length = placedSection.virtualSpan.size := by
  rw [layout.placed_eq] at member
  exact (placed_virtualSize_eq _ _ _ _ _ placedSection member).symm

/-- Same-length replacements retain every consumer-visible coordinate between
two independently checked layouts. Actual section contents remain in each layout;
this theorem neither equates bytes nor asserts preparation succeeds. -/
theorem ImageLayout.coordinates_eq_of_lengths_eq (left right : ImageLayout)
    (sizes : sectionSizes left.requested = sectionSizes right.requested)
    (imports : left.requested.imports = right.requested.imports)
    (entry : left.requested.entryPoint = right.requested.entryPoint) :
    placementSpans left.placed.toList = placementSpans right.placed.toList ∧
    left.entryPointRva = right.entryPointRva ∧
    left.sizeOfImage = right.sizeOfImage ∧
    left.importSectionRva = right.importSectionRva ∧
    (∀ libraryIndex symbolIndex,
      left.importAddressRva? libraryIndex symbolIndex =
        right.importAddressRva? libraryIndex symbolIndex) ∧
    (∀ location, resolveSectionLocation? left.placed location =
      resolveSectionLocation? right.placed location) := by
  have spans := left.placementSpans_eq_of_lengths_eq right sizes imports
  have resolveEq := fun location => resolveSectionLocation?_eq_of_placementSpans_eq
    location spans left.sourceLengths_eq_virtualSizes right.sourceLengths_eq_virtualSizes
  have entryEq : left.entryPointRva = right.entryPointRva := by
    have resolved := resolveEq left.requested.entryPoint
    rw [left.entryPointRva_eq, entry, right.entryPointRva_eq] at resolved
    exact Option.some.inj resolved
  have countEq : left.placed.length = right.placed.length := by
    have count := congrArg List.length spans
    change left.placed.toList.length = right.placed.toList.length
    simpa [placementSpans] using count
  have lastEq := lastVirtualStart_eq_of_spans_eq _ _ spans
  have greatestEq := greatestVirtualEnd_eq_of_spans_eq _ _ spans
  have imageEq : left.sizeOfImage = right.sizeOfImage := by
    rw [left.sizeOfImage_eq, right.sizeOfImage_eq, countEq, greatestEq]
  have importRvaEq : left.importSectionRva = right.importSectionRva := by
    rw [left.importSectionRva_eq, right.importSectionRva_eq, imports, lastEq]
  refine ⟨spans, entryEq, imageEq, importRvaEq, ?_, resolveEq⟩
  intro libraryIndex symbolIndex
  unfold ImageLayout.importAddressRva?
  rw [importRvaEq, left.importLayouts_eq, right.importLayouts_eq, imports]

/-- The proof-carrying plan resolver projects to the same checked coordinate. -/
theorem ImagePlan.resolveSectionLocation?_rva (plan : ImagePlan) (location : SectionLocation) :
    (plan.resolveSectionLocation? location).map (fun resolved => resolved.rva) =
      Grass.Artifact.PE.resolveSectionLocation? plan.layout.placed location := by
  unfold ImagePlan.resolveSectionLocation? Grass.Artifact.PE.resolveSectionLocation?
  split <;> simp_all
  rename_i outside
  rw [Vec.get?_eq_none _ outside]
  rfl

end Grass.Artifact.PE
