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

universe u u₁ u₂

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

/-- Name-indexed compatibility projected from the exact positional placement
checker for use by lowering consumers. -/
def FieldsCompatibleByName (placement : Placement layout policy) : Prop :=
  ∀ placed ∈ layout.fields,
    ∃ selected ∈ placement.fields,
      selected.name = placed.field.name ∧
        policy.accepts placed.field.repr selected.location = true

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

/-- A valid placement inherits nominal uniqueness from its checked layout. -/
theorem fieldNamesNodup_of_wellFormed (placement : Placement layout policy)
    (closed : placement.WellFormed) : placement.fieldNames.Nodup := by
  rw [placement.fieldNamesExact_of_wellFormed closed]
  exact layout.fieldNamesNodup_of_wellFormed
    (placement.layoutWellFormed_of_wellFormed closed)

private theorem eq_of_mem_of_mem_of_map_nodup
    {α : Type u₁} {β : Type u₂} (key : α → β)
    {items : List α} {left right : α}
    (unique : (items.map key).Nodup)
    (leftMem : left ∈ items) (rightMem : right ∈ items)
    (sameKey : key left = key right) : left = right := by
  induction items with
  | nil => simp at leftMem
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at unique
      rw [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          apply unique.1
          rw [sameKey]
          exact List.mem_map.mpr ⟨right, rightMem, rfl⟩
      · rcases rightMem with rfl | rightMem
        · exfalso
          apply unique.1
          rw [← sameKey]
          exact List.mem_map.mpr ⟨left, leftMem, rfl⟩
        · exact ih unique.2 leftMem rightMem

/-- `Placement.field_eq_of_mem_of_mem_of_name_eq` proves that two entries in a
valid placement with the same logical name are the same selected location. -/
theorem field_eq_of_mem_of_mem_of_name_eq
    (placement : Placement layout policy) (left right : FieldLocation Location)
    (closed : placement.WellFormed)
    (leftMem : left ∈ placement.fields) (rightMem : right ∈ placement.fields)
    (sameName : left.name = right.name) : left = right := by
  exact eq_of_mem_of_mem_of_map_nodup FieldLocation.name
    (placement.fieldNamesNodup_of_wellFormed closed) leftMem rightMem sameName

/-- Under `Placement.WellFormed`, nominal lookup returns the exact authored
field-location entry already held by the caller. -/
theorem lookup?_eq_some_of_mem
    (placement : Placement layout policy) (name : Name)
    (field : FieldLocation Location) (closed : placement.WellFormed)
    (member : field ∈ placement.fields) (hasName : field.name = name) :
    placement.lookup? name = some field := by
  have nameMember : name ∈ placement.fieldNames := by
    simp [fieldNames]
    exact ⟨field, member, hasName⟩
  obtain ⟨found, foundLookup⟩ := placement.locationForName name nameMember
  have foundMem := mem_of_lookup? foundLookup
  have foundName := name_of_lookup? foundLookup
  have foundEq : found = field :=
    placement.field_eq_of_mem_of_mem_of_name_eq found field closed
      foundMem member (foundName.trans hasName.symm)
  simpa [foundEq] using foundLookup

private theorem pairsCompatible_by_name
    (policy : LocationPolicy profile Location)
    (placed : List (PlacedField profile))
    (selected : List (FieldLocation Location))
    (namesExact : selected.map FieldLocation.name =
      placed.map fun field => field.field.name)
    (compatible : PairsCompatible policy placed selected) :
    ∀ field ∈ placed,
      ∃ location ∈ selected,
        location.name = field.field.name ∧
          policy.accepts field.field.repr location.location = true := by
  induction placed generalizing selected with
  | nil => simp
  | cons head tail ih =>
      cases selected with
      | nil => simp at namesExact
      | cons selectedHead selectedTail =>
          simp only [List.map_cons, List.cons.injEq] at namesExact
          simp only [PairsCompatible] at compatible
          intro field member
          rw [List.mem_cons] at member
          rcases member with rfl | member
          · exact ⟨selectedHead, by simp, namesExact.1, compatible.1⟩
          · rcases ih selectedTail namesExact.2 compatible.2 field member with
              ⟨location, locationMem, nameExact, accepted⟩
            exact ⟨location, by simp [locationMem], nameExact, accepted⟩

/-- `Placement.fieldsCompatibleByName_of_wellFormed` exposes pointwise policy
acceptance by logical field identity rather than positional list recursion. -/
theorem fieldsCompatibleByName_of_wellFormed
    (placement : Placement layout policy) (closed : placement.WellFormed) :
    placement.FieldsCompatibleByName := by
  apply pairsCompatible_by_name policy layout.fields placement.fields
  · exact placement.fieldNamesExact_of_wellFormed closed
  · exact placement.fieldsCompatible_of_wellFormed closed

/-- A successful nominal lookup in a valid placement satisfies the consumer's
location policy for the corresponding authored layout field. -/
theorem accepts_of_layout_mem_of_lookup
    (placement : Placement layout policy) (closed : placement.WellFormed)
    (placed : PlacedField profile) (placedMem : placed ∈ layout.fields)
    (selected : FieldLocation Location)
    (found : placement.lookup? placed.field.name = some selected) :
    policy.accepts placed.field.repr selected.location = true := by
  rcases placement.fieldsCompatibleByName_of_wellFormed closed placed placedMem with
    ⟨accepted, acceptedMem, acceptedName, policyAccepts⟩
  have selectedMem := mem_of_lookup? found
  have selectedName := name_of_lookup? found
  have selectedEq : selected = accepted :=
    placement.field_eq_of_mem_of_mem_of_name_eq selected accepted closed
      selectedMem acceptedMem (selectedName.trans acceptedName.symm)
  simpa [selectedEq] using policyAccepts

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
