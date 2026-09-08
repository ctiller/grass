import Grass.Construct.Layout.Core

/-!
# Logical-field placement

A placement maps every field of one checked logical layout to a physical
location accepted by an explicit consumer policy.  The location type and policy
are parameters: this layer does not assume registers, stack slots, an ABI, or an
instruction set.
-/

namespace Grass.Construct

open Grass.Core
open Grass.Construct.Layout

universe u

/-- Consumer-supplied compatibility rule between object representations and
physical locations. -/
structure LocationPolicy (profile : LayoutProfile) (Location : Type u) where
  accepts : ObjectRepr profile → Location → Bool

/-- One nominal field-to-location choice. -/
structure FieldLocation (Location : Type u) where
  name : Name
  location : Location
deriving Repr, DecidableEq

/-- Raw placement indexed by the exact layout and compatibility policy it uses. -/
structure Placement {profile : LayoutProfile} {Location : Type u}
    (layout : StructLayout profile) (policy : LocationPolicy profile Location) where
  fields : List (FieldLocation Location)

namespace Placement

variable {profile : LayoutProfile} {Location : Type u}
  {layout : StructLayout profile} {policy : LocationPolicy profile Location}

/-- Selected logical field names in placement order. -/
def fieldNames (placement : Placement layout policy) : List Name :=
  placement.fields.map FieldLocation.name

/-- Find a selected physical location by logical field name. -/
def lookup? (placement : Placement layout policy) (name : Name) :
    Option (FieldLocation Location) :=
  placement.fields.find? fun field => field.name == name

/-- A successful placement lookup has the requested nominal name. -/
theorem name_of_lookup? {placement : Placement layout policy} {name : Name}
    {field : FieldLocation Location} (h : placement.lookup? name = some field) :
    field.name = name := by
  have hmatch : (field.name == name) = true := by
    exact List.find?_some (p := fun candidate : FieldLocation Location =>
      candidate.name == name) (by simpa [lookup?] using h)
  exact LawfulBEq.eq_of_beq hmatch

/-- A successful placement lookup returns an authored placement entry. -/
theorem mem_of_lookup? {placement : Placement layout policy} {name : Name}
    {field : FieldLocation Location} (h : placement.lookup? name = some field) :
    field ∈ placement.fields :=
  List.mem_of_find?_eq_some h

@[simp] theorem lookup?_isSome_iff_mem_fieldNames
    (placement : Placement layout policy) (name : Name) :
    (placement.lookup? name).isSome = true ↔ name ∈ placement.fieldNames := by
  simp [lookup?, fieldNames]

/-- Every selected field name has a concrete location lookup result. -/
theorem locationForName (placement : Placement layout policy) (name : Name)
    (member : name ∈ placement.fieldNames) :
    ∃ field, placement.lookup? name = some field := by
  apply Option.isSome_iff_exists.mp
  exact (placement.lookup?_isSome_iff_mem_fieldNames name).2 member

private def pairsCompatible (policy : LocationPolicy profile Location) :
    List (PlacedField profile) → List (FieldLocation Location) → Bool
  | [], [] => true
  | placed :: placedRest, selected :: selectedRest =>
      policy.accepts placed.field.repr selected.location &&
        pairsCompatible policy placedRest selectedRest
  | _, _ => false

/-- Proposition-level pointwise compatibility in exact layout/placement order. -/
def PairsCompatible (policy : LocationPolicy profile Location) :
    List (PlacedField profile) → List (FieldLocation Location) → Prop
  | [], [] => True
  | placed :: placedRest, selected :: selectedRest =>
      policy.accepts placed.field.repr selected.location = true ∧
        PairsCompatible policy placedRest selectedRest
  | _, _ => False

private theorem pairsCompatible_eq_true_iff
    (policy : LocationPolicy profile Location)
    (placed : List (PlacedField profile))
    (selected : List (FieldLocation Location)) :
    pairsCompatible policy placed selected = true ↔
      PairsCompatible policy placed selected := by
  induction placed generalizing selected with
  | nil => cases selected <;> simp [pairsCompatible, PairsCompatible]
  | cons head tail ih =>
      cases selected <;> simp [pairsCompatible, PairsCompatible, ih]

/-- Compatibility of corresponding layout fields and selected locations. -/
def fieldsCompatible (placement : Placement layout policy) : Bool :=
  pairsCompatible policy layout.fields placement.fields

/-- Certificate-facing compatibility of every corresponding field/location pair. -/
def FieldsCompatible (placement : Placement layout policy) : Prop :=
  PairsCompatible policy layout.fields placement.fields

@[simp] theorem fieldsCompatible_eq_true_iff
    (placement : Placement layout policy) :
    placement.fieldsCompatible = true ↔ placement.FieldsCompatible := by
  exact pairsCompatible_eq_true_iff policy layout.fields placement.fields

/-- Executable placement checker.  `Placement.wellFormed` uses exact nominal
order to reject missing, duplicate, extra, or reordered field assignments. -/
def wellFormed (placement : Placement layout policy) : Bool :=
  layout.wellFormed &&
  decide (placement.fieldNames = layout.fieldNames) &&
  placement.fieldsCompatible

/-- Certificate-facing statement for `Placement.wellFormed`. -/
def WellFormed (placement : Placement layout policy) : Prop :=
  placement.wellFormed = true

instance (placement : Placement layout policy) : Decidable placement.WellFormed :=
  inferInstanceAs (Decidable (placement.wellFormed = true))

/-- Public decomposition of exact placement closure. -/
@[simp] theorem wellFormed_iff (placement : Placement layout policy) :
    placement.WellFormed ↔
      (layout.WellFormed ∧ placement.fieldNames = layout.fieldNames) ∧
        placement.FieldsCompatible := by
  simp [WellFormed, wellFormed, StructLayout.WellFormed]

theorem layoutWellFormed_of_wellFormed (placement : Placement layout policy)
    (h : placement.WellFormed) : layout.WellFormed :=
  (wellFormed_iff placement).mp h |>.1.1

theorem fieldNamesExact_of_wellFormed (placement : Placement layout policy)
    (h : placement.WellFormed) : placement.fieldNames = layout.fieldNames :=
  (wellFormed_iff placement).mp h |>.1.2

theorem fieldsCompatible_of_wellFormed (placement : Placement layout policy)
    (h : placement.WellFormed) : placement.FieldsCompatible :=
  (wellFormed_iff placement).mp h |>.2

/-- Every logical field in a well-formed placement has a concrete selected
physical location. -/
theorem locationForLayoutField (placement : Placement layout policy)
    (h : placement.WellFormed) (name : Name)
    (member : name ∈ layout.fieldNames) :
    ∃ field, placement.lookup? name = some field := by
  apply placement.locationForName name
  rw [placement.fieldNamesExact_of_wellFormed h]
  exact member

end Placement

end Grass.Construct
