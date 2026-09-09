import Grass.Artifact.PE.Imports

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

/-- Arithmetic obligations for the canonical executable adapter. -/
def ExecutableImageDescription.Writable
    (description : ExecutableImageDescription) : Prop :=
  let materialized := materializeImports description
  importLibrariesValid description.imports.toList = true ∧
  materialized.sections.length < 2 ^ 16 ∧
  placementsFitU32 (placeImageSections materialized).toList = true

instance (description : ExecutableImageDescription) : Decidable description.Writable := by
  unfold ExecutableImageDescription.Writable
  infer_instance

/-- A writable description has a representable COFF section count. -/
theorem ExecutableImageDescription.Writable.sectionCountFits
    {description : ExecutableImageDescription} (writable : description.Writable) :
    (materializeImports description).sections.length < 2 ^ 16 :=
  writable.2.1

/-- A writable description has no placement that would truncate into its PE
field. -/
theorem ExecutableImageDescription.Writable.placementsFit
    {description : ExecutableImageDescription} (writable : description.Writable) :
    placementsFitU32
      (placeImageSections (materializeImports description)).toList = true :=
  writable.2.2

/-- A writable description has only nonempty, terminator-free import names and
at least one symbol per imported library. -/
theorem ExecutableImageDescription.Writable.importsValid
    {description : ExecutableImageDescription} (writable : description.Writable) :
    importLibrariesValid description.imports.toList = true :=
  writable.1

end Grass.Artifact.PE
