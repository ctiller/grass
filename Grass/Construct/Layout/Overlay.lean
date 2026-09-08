import Grass.Construct.Layout.Core

/-!
# Explicit overlay layouts

`OverlayLayout` is the separate constructor for union-like representations.
Every member begins at byte zero by construction, while
`OverlayLayout.memberWellFormed` checks that the selected aggregate extent and
alignment contain and admit every member representation.  Ordinary
`StructLayout.fieldsDisjoint` remains unchanged.
-/

namespace Grass.Construct.Layout

open Grass.Core Grass.Memory

/-- A union-like collection of named representations sharing byte offset zero. -/
structure OverlayLayout (profile : LayoutProfile) where
  members : List (FieldSpec profile)
  size : Nat
  alignment : Nat
deriving Repr, DecidableEq

namespace OverlayLayout

variable {profile : LayoutProfile}

/-- Overlay member names in declaration order. -/
def memberNames (layout : OverlayLayout profile) : List Name :=
  layout.members.map FieldSpec.name

/-- Exact range occupied when one overlay member is selected. -/
def memberRange (member : FieldSpec profile) : ByteRange :=
  ⟨0, member.repr.size⟩

/-- Find a member representation by its nominal name. -/
def lookup? (layout : OverlayLayout profile) (name : Name) :
    Option (FieldSpec profile) :=
  layout.members.find? (fun member => member.name == name)

/-- A successful lookup returns the requested nominal member. -/
theorem name_of_lookup? {layout : OverlayLayout profile} {name : Name}
    {member : FieldSpec profile} (h : layout.lookup? name = some member) :
    member.name = name := by
  have hmatch : (member.name == name) = true := by
    exact List.find?_some (p := fun candidate : FieldSpec profile =>
      candidate.name == name) (by simpa [lookup?] using h)
  exact LawfulBEq.eq_of_beq hmatch

/-- A successful lookup returns a declared overlay member. -/
theorem mem_of_lookup? {layout : OverlayLayout profile} {name : Name}
    {member : FieldSpec profile} (h : layout.lookup? name = some member) :
    member ∈ layout.members :=
  List.mem_of_find?_eq_some h

@[simp] theorem lookup?_isSome_iff_mem_memberNames
    (layout : OverlayLayout profile) (name : Name) :
    (layout.lookup? name).isSome = true ↔ name ∈ layout.memberNames := by
  simp [lookup?, memberNames]

/-- Every declared overlay member name has a concrete representation lookup. -/
theorem memberForName (layout : OverlayLayout profile) (name : Name)
    (member : name ∈ layout.memberNames) :
    ∃ field, layout.lookup? name = some field := by
  apply Option.isSome_iff_exists.mp
  exact (layout.lookup?_isSome_iff_mem_memberNames name).2 member

/-- Local representation, containment, and aggregate-compatibility check. -/
def memberWellFormed (layout : OverlayLayout profile)
    (member : FieldSpec profile) : Bool :=
  decide (0 < member.repr.size) &&
  member.repr.wellFormed &&
  decide (memberRange member |>.WithinBound layout.size) &&
  decide (layout.alignment % member.repr.alignment = 0)

/-- Proposition-level representation and containment obligations for one member. -/
def MemberWellFormed (layout : OverlayLayout profile)
    (member : FieldSpec profile) : Prop :=
  0 < member.repr.size ∧
  member.repr.WellFormed ∧
  (memberRange member).WithinBound layout.size ∧
  layout.alignment % member.repr.alignment = 0

@[simp] theorem memberWellFormed_eq_true_iff
    (layout : OverlayLayout profile) (member : FieldSpec profile) :
    layout.memberWellFormed member = true ↔ layout.MemberWellFormed member := by
  simp [memberWellFormed, MemberWellFormed, ObjectRepr.WellFormed, and_assoc]

/-- Proposition-level validity of every declared overlay member. -/
def MembersWellFormed (layout : OverlayLayout profile) : Prop :=
  ∀ member ∈ layout.members, layout.MemberWellFormed member

@[simp] theorem membersAll_eq_true_iff (layout : OverlayLayout profile) :
    layout.members.all layout.memberWellFormed = true ↔
      layout.MembersWellFormed := by
  simp [MembersWellFormed]

/-- Executable checker for one nonempty union-like overlay. -/
def wellFormed (layout : OverlayLayout profile) : Bool :=
  decide (layout.members ≠ []) &&
  decide layout.memberNames.Nodup &&
  decide (0 < layout.alignment) &&
  profile.acceptsAlignment layout.alignment &&
  decide (IsAligned layout.size layout.alignment) &&
  layout.members.all layout.memberWellFormed

/-- Certificate-facing statement for `OverlayLayout.wellFormed`. -/
def WellFormed (layout : OverlayLayout profile) : Prop :=
  layout.wellFormed = true

instance (layout : OverlayLayout profile) : Decidable layout.WellFormed :=
  inferInstanceAs (Decidable (layout.wellFormed = true))

/-- Public decomposition of overlay-layout closure. -/
@[simp] theorem wellFormed_iff (layout : OverlayLayout profile) :
    layout.WellFormed ↔
      (((((layout.members ≠ [] ∧ layout.memberNames.Nodup) ∧
        0 < layout.alignment) ∧
        profile.acceptsAlignment layout.alignment = true) ∧
        IsAligned layout.size layout.alignment) ∧
        layout.MembersWellFormed) := by
  simp [WellFormed, wellFormed, MembersWellFormed]

theorem memberNamesNodup_of_wellFormed (layout : OverlayLayout profile)
    (h : layout.WellFormed) : layout.memberNames.Nodup :=
  (wellFormed_iff layout).mp h |>.1.1.1.1.2

theorem membersNonempty_of_wellFormed (layout : OverlayLayout profile)
    (h : layout.WellFormed) : layout.members ≠ [] :=
  (wellFormed_iff layout).mp h |>.1.1.1.1.1

theorem aggregateAlignmentPositive_of_wellFormed (layout : OverlayLayout profile)
    (h : layout.WellFormed) : 0 < layout.alignment :=
  (wellFormed_iff layout).mp h |>.1.1.1.2

theorem profileAcceptsAlignment_of_wellFormed (layout : OverlayLayout profile)
    (h : layout.WellFormed) :
    profile.acceptsAlignment layout.alignment = true :=
  (wellFormed_iff layout).mp h |>.1.1.2

theorem sizeAligned_of_wellFormed (layout : OverlayLayout profile)
    (h : layout.WellFormed) : IsAligned layout.size layout.alignment :=
  (wellFormed_iff layout).mp h |>.1.2

theorem membersWellFormed_of_wellFormed (layout : OverlayLayout profile)
    (h : layout.WellFormed) : layout.MembersWellFormed :=
  (wellFormed_iff layout).mp h |>.2

theorem memberWellFormed_of_wellFormed (layout : OverlayLayout profile)
    (h : layout.WellFormed) (member : FieldSpec profile)
    (memberOf : member ∈ layout.members) : layout.MemberWellFormed member :=
  layout.membersWellFormed_of_wellFormed h member memberOf

end OverlayLayout

end Grass.Construct.Layout
