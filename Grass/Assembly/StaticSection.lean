import Grass.Assembly.StaticSectionPacking
import Grass.Artifact.PE.Validation

/-! Deterministic packing of logical static declarations into
one caller-selected PE section. It does not choose the section's PE placement. -/
namespace Grass.Assembly.StaticSection

open Grass.Artifact.PE Grass.Assembly.StaticObjects Grass.Std.Logical

structure Layout (table : Table) where
  private mk ::
  objects : List Object
  rawSection : RawSection
  objectsExact : objects = (packFrom 0 table.declarations).1
  declarationsExact : objects.map Object.declaration = table.declarations
  contentsExact : rawSection.contents = (packFrom 0 table.declarations).2
  offsetsAligned : objects.all (fun object => decide
    (object.offset % object.declaration.alignment = 0)) = true
  ordered : ordered? objects = true
  payloadsExact : objects.all (fun object => decide
    ((rawSection.contents.drop object.offset).take object.declaration.bytes.length =
      object.declaration.bytes)) = true
  contained : objects.all (fun object => decide
    (object.endOffset ≤ rawSection.contents.length)) = true

def layout? (table : Table) (name : SectionName) (characteristics : BitVec 32) :
    Option (Layout table) :=
  let packed := packFrom 0 table.declarations
  let rawSection : RawSection := { name, contents := packed.2, characteristics }
  some ⟨packed.1, rawSection, rfl, packFrom_declarations 0 table.declarations,
    rfl, Table.packFrom_offsetsAligned_all table, packFrom_ordered 0 table.declarations,
    packFrom_zero_payloads_all table.declarations,
    packFrom_zero_contained_all table.declarations⟩

theorem layout?_isSome (table : Table) (name : SectionName)
    (characteristics : BitVec 32) : (layout? table name characteristics).isSome = true := rfl
def Layout.lookup? {table : Table} (layout : Layout table) (name : String) : Option Object :=
  layout.objects.find? fun object => object.declaration.name = name

theorem Layout.lookup?_member {table : Table} {layout : Layout table}
    {name : String} {object : Object} (found : layout.lookup? name = some object) :
    object ∈ layout.objects :=
  List.mem_of_find?_eq_some found

theorem Layout.lookup?_name {table : Table} {layout : Layout table}
    {name : String} {object : Object} (found : layout.lookup? name = some object) :
    object.declaration.name = name := by
  simpa [Layout.lookup?] using List.find?_some found

theorem Layout.namesUnique {table : Table} (layout : Layout table) :
    (layout.objects.map (fun object => object.declaration.name)).Nodup := by
  have unique := table.names_unique
  rw [← layout.declarationsExact] at unique
  simp only [List.map_map] at unique
  have functionEq : Declaration.name ∘ Object.declaration =
      (fun object => object.declaration.name) := by
    funext object
    rfl
  rw [functionEq] at unique
  exact unique

theorem Layout.lookup?_complete {table : Table} (layout : Layout table)
    {object : Object} (member : object ∈ layout.objects) :
    layout.lookup? object.declaration.name = some object :=
  Grass.Std.Logical.find?_key_of_mem layout.namesUnique member

theorem Layout.objectContained {table : Table} (layout : Layout table)
    {object : Object} (member : object ∈ layout.objects) :
    object.endOffset ≤ layout.rawSection.contents.length := by
  have all := List.all_eq_true.mp layout.contained object member
  exact of_decide_eq_true all

theorem layout?_rawSection {table : Table} {name : SectionName}
    {characteristics : BitVec 32} {layout : Layout table}
    (success : layout? table name characteristics = some layout) :
    layout.rawSection.name = name ∧
      layout.rawSection.characteristics = characteristics ∧
      layout.rawSection.contents = (packFrom 0 table.declarations).2 := by
  simp only [layout?] at success
  cases success
  exact ⟨rfl, rfl, rfl⟩

structure ObjectSpan (plan : ImagePlan) {table : Table} (layout : Layout table)
    (sectionIndex : Nat) (requestedName : String) (object : Object) where
  objectMember : object ∈ layout.objects
  nameExact : object.declaration.name = requestedName
  placedSection : PlacedSection
  selected : plan.layout.placed.get? sectionIndex = some placedSection
  sourceExact : placedSection.source = layout.rawSection
  endInBounds : object.endOffset ≤ placedSection.source.contents.length
  rva : Nat
  rva_eq : rva = placedSection.virtualSpan.start + object.offset
  rvaFits : rva < 2 ^ 32
  rvaAligned : rva % object.declaration.alignment = 0

def resolveSpan? (plan : ImagePlan) {table : Table} (layout : Layout table)
    (sectionIndex : Nat) (name : String) :
    Option (Sigma fun object => ObjectSpan plan layout sectionIndex name object) :=
  match found : layout.lookup? name with
  | none => none
  | some object =>
    match selected : plan.layout.placed.get? sectionIndex with
    | none => none
    | some placedSection =>
      if sourceExact : placedSection.source = layout.rawSection then
        if endInBounds : object.endOffset ≤ placedSection.source.contents.length then
          let rva := placedSection.virtualSpan.start + object.offset
          have placedMember : placedSection ∈ plan.layout.placed.toList :=
            (Grass.Std.Logical.Vec.mem_iff_exists_get?).mpr ⟨sectionIndex, selected⟩
          have virtualEnd := (plan.writable.placementFields placedMember).2.2.1
          have virtualSize := plan.placedVirtualSize placedMember
          have offsetBound : object.offset ≤ placedSection.source.contents.length := by
            simp only [Object.endOffset] at endInBounds
            omega
          have rvaFits : rva < 2 ^ 32 := by
            simp only [FileSpan.endOffset] at virtualEnd
            omega
          if rvaAligned : rva % object.declaration.alignment = 0 then
            some ⟨object, layout.lookup?_member found, layout.lookup?_name found,
              placedSection, selected, sourceExact, endInBounds, rva, rfl, rvaFits, rvaAligned⟩
          else none
        else none
      else none

theorem resolveSpan?_name {plan : ImagePlan} {table : Table} {layout : Layout table}
    {sectionIndex : Nat} {name : String}
    {result : Sigma fun object => ObjectSpan plan layout sectionIndex name object}
    (_success : resolveSpan? plan layout sectionIndex name = some result) :
    result.1.declaration.name = name := by
  exact result.2.nameExact

theorem resolveSpan?_lookup {plan : ImagePlan} {table : Table} {layout : Layout table}
    {sectionIndex : Nat} {name : String}
    {result : Sigma fun object => ObjectSpan plan layout sectionIndex name object}
    (_success : resolveSpan? plan layout sectionIndex name = some result) :
    layout.lookup? name = some result.1 := by
  calc
    layout.lookup? name = layout.lookup? result.1.declaration.name := by
      exact congrArg layout.lookup? result.2.nameExact.symm
    _ = some result.1 := layout.lookup?_complete result.2.objectMember

def ObjectSpan.byteLength {plan : ImagePlan} {table : Table} {layout : Layout table}
    {sectionIndex : Nat} {requestedName : String} {object : Object}
    (_span : ObjectSpan plan layout sectionIndex requestedName object) : Nat :=
  object.declaration.bytes.length

theorem ObjectSpan.nonempty_resolvesLocation {plan : ImagePlan} {table : Table}
    {layout : Layout table} {sectionIndex : Nat} {object : Object}
    {requestedName : String} (span : ObjectSpan plan layout sectionIndex requestedName object)
    (nonempty : 0 < object.declaration.bytes.length) :
    (plan.resolveSectionLocation? ⟨sectionIndex, object.offset⟩).isSome = true := by
  have offsetInBounds : object.offset < span.placedSection.source.contents.length := by
    have bounded := span.endInBounds
    simp only [Object.endOffset] at bounded
    omega
  unfold ImagePlan.resolveSectionLocation?
  split
  next selected =>
    rw [span.selected] at selected
    contradiction
  next placedSection selected =>
    have same : placedSection = span.placedSection := by
      exact Option.some.inj (selected.symm.trans span.selected)
    subst placedSection
    simp [offsetInBounds]

end Grass.Assembly.StaticSection
