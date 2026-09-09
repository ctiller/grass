import Grass.Artifact.PE.Exceptions

/-!
# PE image representability validation

Layout arithmetic remains in unbounded `Nat`. This module is the mandatory gate
before those coordinates are serialized into 16- and 32-bit PE fields: no
successful writer may rely on `BitVec.ofNat` truncation as validation.
-/

namespace Grass.Artifact.PE

/-- `placementFitsU32` checks every serialized coordinate and extent, including
each exclusive end, against the 32-bit PE field bound. -/
def placementFitsU32 (placed : PlacedSection) : Bool :=
  decide (placed.virtualSpan.start < 2 ^ 32) &&
  decide (placed.virtualSpan.size < 2 ^ 32) &&
  decide (placed.virtualSpan.endOffset < 2 ^ 32) &&
  decide (placed.rawSpan.start < 2 ^ 32) &&
  decide (placed.rawSpan.size < 2 ^ 32) &&
  decide (placed.rawSpan.endOffset < 2 ^ 32)

/-- Check every placement without allocating from any attacker-controlled
serialized count. -/
def placementsFitU32 : List PlacedSection → Bool
  | [] => true
  | placed :: tail => placementFitsU32 placed && placementsFitU32 tail

/-- A successful placement check exposes every individual serialized bound. -/
theorem placementFitsU32_fields {placed : PlacedSection}
    (fits : placementFitsU32 placed = true) :
    placed.virtualSpan.start < 2 ^ 32 ∧
    placed.virtualSpan.size < 2 ^ 32 ∧
    placed.virtualSpan.endOffset < 2 ^ 32 ∧
    placed.rawSpan.start < 2 ^ 32 ∧
    placed.rawSpan.size < 2 ^ 32 ∧
    placed.rawSpan.endOffset < 2 ^ 32 := by
  simp [placementFitsU32, Bool.and_eq_true, decide_eq_true_eq] at fits
  rcases fits with ⟨⟨⟨⟨⟨virtualStart, virtualSize⟩, virtualEnd⟩, rawStart⟩,
    rawSize⟩, rawEnd⟩
  exact ⟨virtualStart, virtualSize, virtualEnd, rawStart, rawSize, rawEnd⟩

/-- Every member of a successfully checked list has checked field bounds. -/
theorem placementsFitU32_member {placements : List PlacedSection}
    (fits : placementsFitU32 placements = true) {placed : PlacedSection}
    (member : placed ∈ placements) : placementFitsU32 placed = true := by
  induction placements with
  | nil => simp at member
  | cons head tail ih =>
      simp only [placementsFitU32, Bool.and_eq_true] at fits
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact fits.1
      · exact ih fits.2 member

/-- Final table-byte validation when an exception table was requested. -/
def ImageLayout.ExceptionsValid (layout : ImageLayout) : Prop :=
  match layout.requested.exceptionTable with
  | none => True
  | some description => exceptionTableValid layout.placed description = true

instance (layout : ImageLayout) : Decidable layout.ExceptionsValid := by
  unfold ImageLayout.ExceptionsValid
  split <;> infer_instance

/-- Representability, import and exception-table obligations for one layout. -/
def ImageLayout.Writable (layout : ImageLayout) : Prop :=
  importLibrariesValid layout.requested.imports.toList = true ∧
  layout.ImportsResolved ∧
  layout.materialized.sections.length < 2 ^ 16 ∧
  placementsFitU32 layout.placed.toList = true ∧
  layout.entryPointRva < 2 ^ 32 ∧
  layout.sizeOfImage < 2 ^ 32 ∧ layout.ExceptionsValid

instance (layout : ImageLayout) : Decidable layout.Writable := by
  unfold ImageLayout.Writable
  infer_instance

/-- A writable description has a representable COFF section count. -/
theorem ImageLayout.Writable.sectionCountFits
    {layout : ImageLayout} (writable : layout.Writable) :
    layout.materialized.sections.length < 2 ^ 16 :=
  writable.2.2.1

/-- The derived aligned header extent is representable in `SizeOfHeaders`. -/
theorem ImageLayout.Writable.headerSizeFits
    {layout : ImageLayout} (writable : layout.Writable) :
    firstRawOffset canonicalPeOffset layout.placed.length canonicalFileAlignment <
      2 ^ 32 := by
  have countEq : layout.placed.length = layout.materialized.sections.length := by
    rw [layout.placed_eq]
    exact placeImageSections_length _
  rw [countEq]
  have countFits := writable.sectionCountFits
  have alignedBound := alignUp_lt_add
    (ntHeadersSpan canonicalPeOffset layout.materialized.sections.length).endOffset
    (by decide : 0 < canonicalFileAlignment)
  calc
    firstRawOffset canonicalPeOffset layout.materialized.sections.length
        canonicalFileAlignment <
        (ntHeadersSpan canonicalPeOffset layout.materialized.sections.length).endOffset +
          canonicalFileAlignment := alignedBound
    _ < 2 ^ 32 := by
      simp [ntHeadersSpan, ntHeadersSize, FileSpan.endOffset, canonicalPeOffset,
        peSignatureSize, coffHeaderSize, optionalHeader64Size, sectionHeaderSize,
        canonicalFileAlignment]
      omega

/-- A writable description has no placement that would truncate into its PE
field. -/
theorem ImageLayout.Writable.placementsFit
    {layout : ImageLayout} (writable : layout.Writable) :
    placementsFitU32 layout.placed.toList = true :=
  writable.2.2.2.1

/-- A writable description has only nonempty, terminator-free import names and
at least one symbol per imported library. -/
theorem ImageLayout.Writable.importsValid
    {layout : ImageLayout} (writable : layout.Writable) :
    importLibrariesValid layout.requested.imports.toList = true :=
  writable.1

/-- Import records and IAT slots contain addresses from this final placement. -/
theorem ImageLayout.Writable.importsResolved
    {layout : ImageLayout} (writable : layout.Writable) : layout.ImportsResolved :=
  writable.2.1

/-- Every placed PE field is safe to narrow to its serialized width. -/
theorem ImageLayout.Writable.placementFields
    {layout : ImageLayout} (writable : layout.Writable)
    {placed : PlacedSection} (member : placed ∈ layout.placed.toList) :
    placed.virtualSpan.start < 2 ^ 32 ∧
    placed.virtualSpan.size < 2 ^ 32 ∧
    placed.virtualSpan.endOffset < 2 ^ 32 ∧
    placed.rawSpan.start < 2 ^ 32 ∧
    placed.rawSpan.size < 2 ^ 32 ∧
    placed.rawSpan.endOffset < 2 ^ 32 :=
  placementFitsU32_fields (placementsFitU32_member writable.placementsFit member)

/-- A checked layout packages the one placement used by every writer field. -/
structure ImagePlan where
  layout : ImageLayout
  writable : layout.Writable

/-- The production plan validates any explicitly requested exception table. -/
theorem ImagePlan.exceptionsValid (plan : ImagePlan) : plan.layout.ExceptionsValid :=
  plan.writable.2.2.2.2.2.2

/-- A checked section-relative address and the evidence needed by source and
relocation consumers. -/
structure ResolvedSectionLocation (plan : ImagePlan) (location : SectionLocation) where
  placedSection : PlacedSection
  selected : plan.layout.placed.get? location.sectionIndex = some placedSection
  offsetInBounds : location.offset < placedSection.source.contents.length
  rva : Nat
  rva_eq : rva = placedSection.virtualSpan.start + location.offset
  rvaFits : rva < 2 ^ 32

/-- Every section in a checked plan retains its source byte length as its
virtual extent. -/
theorem ImagePlan.placedVirtualSize (plan : ImagePlan) {placedSection : PlacedSection}
    (member : placedSection ∈ plan.layout.placed.toList) :
    placedSection.virtualSpan.size = placedSection.source.contents.length := by
  rw [plan.layout.placed_eq] at member
  exact placed_virtualSize_eq _ _ _ _ _ placedSection member

/-- Resolve an in-bounds source location through the checked image layout. -/
def ImagePlan.resolveSectionLocation? (plan : ImagePlan)
    (location : SectionLocation) : Option (ResolvedSectionLocation plan location) :=
  match selected : plan.layout.placed.get? location.sectionIndex with
  | none => none
  | some placedSection =>
      if inBounds : location.offset < placedSection.source.contents.length then
        let rva := placedSection.virtualSpan.start + location.offset
        some {
          placedSection
          selected
          offsetInBounds := inBounds
          rva
          rva_eq := rfl
          rvaFits := by
            have member : placedSection ∈ plan.layout.placed.toList :=
              (Grass.Std.Logical.Vec.mem_iff_exists_get?).mpr
                ⟨location.sectionIndex, selected⟩
            have virtualEnd := (plan.writable.placementFields member).2.2.1
            have virtualSize := plan.placedVirtualSize member
            simp only [FileSpan.endOffset] at virtualEnd
            omega }
      else none

/-- Resolve the base RVA of a nonempty selected section. -/
def ImagePlan.resolveSectionBase? (plan : ImagePlan)
    (sectionIndex : Nat) : Option (ResolvedSectionLocation plan ⟨sectionIndex, 0⟩) :=
  plan.resolveSectionLocation? ⟨sectionIndex, 0⟩

/-- Resolve and validate the only layout accepted by the production writer. -/
def prepareImage (description : ExecutableImageDescription) : Except String ImagePlan :=
  match resolveImageLayout? description with
  | none => .error "PE entry location is outside its requested section"
  | some layout =>
      if writable : layout.Writable then .ok ⟨layout, writable⟩
      else .error "PE image layout, imports or exception table fail the supported profile"

/-- A prepared image's raw payloads begin at the aligned header end and are
contiguous in serialized section order. -/
theorem ImagePlan.rawContiguous (plan : ImagePlan) :
    RawContiguous
      (firstRawOffset canonicalPeOffset plan.layout.materialized.sections.length
        canonicalFileAlignment)
      plan.layout.placed.toList := by
  rw [plan.layout.placed_eq]
  change RawContiguous _ (placeSectionsFrom _ _ _ _ _)
  apply placeSectionsFrom_rawContiguous
  · decide
  · exact alignUp_mod_eq_zero _ (by decide)

end Grass.Artifact.PE
