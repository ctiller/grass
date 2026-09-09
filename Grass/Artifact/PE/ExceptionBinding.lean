import Grass.Artifact.PE.ImageRoundTrip
import Grass.Artifact.PE.ExceptionReader

/-! Connect the checked image's directory to its exact backed runtime table.
ABI meaning of unwind bytes and actual loader behavior remain external inputs. -/
namespace Grass.Artifact.PE

open Grass.Grammar Grass.Std.Logical

/-- A complete nonempty extent resolves its first byte through the same
location resolver used by header directories. -/
theorem resolveSectionExtent?_location {placed : Vec PlacedSection} {extent : SectionExtent}
    {rva : Nat} {bytes : Std.Logical.ByteArray}
    (success : resolveSectionExtent? placed extent = some (rva, bytes)) :
    resolveSectionLocation? placed extent.location = some rva := by
  obtain ⟨placedSection, selected, positive, bounds, address, _, _, _⟩ :=
    resolveSectionExtent?_success success
  simp only [resolveSectionLocation?, selected]
  change (if extent.location.offset < placedSection.source.contents.length then
    some (placedSection.virtualSpan.start + extent.location.offset) else none) = some rva
  rw [if_pos (by omega : extent.location.offset < placedSection.source.contents.length)]
  exact congrArg some address.symm

/-- A requested exception table is validated by the production plan itself. -/
theorem ImagePlan.exceptionTable_evidence (plan : ImagePlan)
    {description : ExceptionTableDescription}
    (requested : plan.layout.requested.exceptionTable = some description) :
    Nonempty (ExceptionTableEvidence plan.layout.placed description) := by
  have valid := plan.exceptionsValid
  unfold ImageLayout.ExceptionsValid at valid
  rw [requested] at valid
  exact exceptionTableValid_evidence valid

/-- The decoded image directory points to the same checked table slice that
the independent runtime reader recovers, with no narrowing loss. -/
theorem ImagePlan.exceptionTable_binding (plan : ImagePlan)
    {description : ExceptionTableDescription}
    (requested : plan.layout.requested.exceptionTable = some description) :
    ∃ evidence : ExceptionTableEvidence plan.layout.placed description,
      plan.layout.exceptionDirectory = (evidence.tableRva, description.table.size) ∧
      plan.expectedImage.optional.exceptionRva.toNat = evidence.tableRva ∧
      plan.expectedImage.optional.exceptionSize.toNat = description.table.size ∧
      readRuntimeTable evidence.tableBytes =
        .done (evidence.functions.map ResolvedRuntimeFunction.expectedRecord) Vec.empty := by
  obtain ⟨evidence⟩ := plan.exceptionTable_evidence requested
  have location := resolveSectionExtent?_location evidence.tableResolved
  obtain ⟨placedSection, selected, positive, bounds, address, finish, bytes, length⟩ :=
    resolveSectionExtent?_success evidence.tableResolved
  have rvaBound : evidence.tableRva < 2^32 := by omega
  have sizeBound : description.table.size < 2^32 := by omega
  have directory : plan.layout.exceptionDirectory =
      (evidence.tableRva, description.table.size) := by
    simp [ImageLayout.exceptionDirectory, requested, location]
  refine ⟨evidence, directory, ?_, ?_, ?_⟩
  · simp [ImagePlan.expectedImage, expectedOptionalHeader, directory,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt rvaBound]
  · simp [ImagePlan.expectedImage, expectedOptionalHeader, directory,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt sizeBound]
  · rw [evidence.tableBytesExact]
    exact readRuntimeTable_write evidence.functions

end Grass.Artifact.PE
