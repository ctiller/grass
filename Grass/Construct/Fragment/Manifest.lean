import Grass.Construct.Fragment.Source

/-!
# Derived fragment manifests and closure

References, citations, and other finite instruction demands use one generic
projection.  The occurrence manifest is derived from exact expanded source;
authors supply only the finite available set against which closure is checked.
-/

namespace Grass.Construct.Fragment

universe u v

/-- Consumer-supplied projection from one instruction to its ordered demands. -/
structure ManifestModel (Instruction : Type u) (Item : Type v) where
  project : Instruction → List Item

namespace Source

variable {Instruction : Type u} {Item : Type v}

/-- Occurrence-exact manifest derived from flat source expansion.  Repeated
demands remain repeated rather than being set-deduplicated. -/
def manifest (source : Source Instruction) (model : ManifestModel Instruction Item) :
    List Item :=
  source.expand.flatMap model.project

@[simp] theorem manifest_literal (instructions : List Instruction)
    (model : ManifestModel Instruction Item) :
    (Source.literal instructions).manifest model = instructions.flatMap model.project := by
  simp [manifest]

@[simp] theorem manifest_generated (id : FragmentId) (body : Source Instruction)
    (model : ManifestModel Instruction Item) :
    (Source.generated id body).manifest model = body.manifest model := by
  simp [manifest]

@[simp] theorem manifest_sequence (children : List (Source Instruction))
    (model : ManifestModel Instruction Item) :
    (Source.sequence children).manifest model =
      children.flatMap fun child => child.manifest model := by
  induction children with
  | nil => simp [manifest]
  | cons child rest ih =>
      have ih' :
          (rest.flatMap Source.expand).flatMap model.project =
            rest.flatMap fun child => child.manifest model := by
        simpa only [manifest, Source.expand_sequence] using ih
      simp [manifest, Source.expand_sequence, ih']

end Source

/-- Available manifest items selected explicitly for one source. -/
structure ManifestClosure {Instruction : Type u} {Item : Type v}
    (source : Source Instruction) (model : ManifestModel Instruction Item) where
  available : List Item

namespace ManifestClosure

variable {Instruction : Type u} {Item : Type v}
  {source : Source Instruction} {model : ManifestModel Instruction Item}
  [DecidableEq Item]

/-- Demanded occurrences absent from the selected available set. -/
def unresolved (closure : ManifestClosure source model) : List Item :=
  (source.manifest model).filter fun item => decide (item ∉ closure.available)

/-- Executable closure check.  The available set is canonical and every
derived occurrence must resolve; extra available items are permitted because a
platform plan may serve several sibling fragments. -/
def wellFormed (closure : ManifestClosure source model) : Bool :=
  decide closure.available.Nodup && closure.unresolved.isEmpty

/-- Certificate-facing statement for `ManifestClosure.wellFormed`. -/
def WellFormed (closure : ManifestClosure source model) : Prop :=
  closure.wellFormed = true

instance (closure : ManifestClosure source model) : Decidable closure.WellFormed :=
  inferInstanceAs (Decidable (closure.wellFormed = true))

/-- Public decomposition of manifest closure. -/
@[simp] theorem wellFormed_iff (closure : ManifestClosure source model) :
    closure.WellFormed ↔
      closure.available.Nodup ∧ closure.unresolved = [] := by
  simp [WellFormed, wellFormed]

end ManifestClosure

end Grass.Construct.Fragment
