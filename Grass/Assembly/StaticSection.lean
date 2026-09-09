import Grass.Assembly.StaticObjects
import Grass.Artifact.PE.Validation

/-! Deterministic packing of logical static declarations into
one caller-selected PE section. It does not choose the section's PE placement. -/
namespace Grass.Assembly.StaticSection

open Grass.Artifact.PE Grass.Assembly.StaticObjects Grass.Std.Logical

structure Object where
  declaration : Declaration
  offset : Nat
deriving DecidableEq, Repr

def Object.endOffset (object : Object) : Nat :=
  object.offset + object.declaration.bytes.length

def packFrom (cursor : Nat) : List Declaration → List Object × Grass.Std.Logical.ByteArray
  | [] => ([], Vec.empty)
  | declaration :: tail =>
      let offset := alignUp cursor declaration.alignment
      let object := { declaration, offset }
      let packedTail := packFrom object.endOffset tail
      (object :: packedTail.1,
        Vec.replicate (offset - cursor) 0 ++ declaration.bytes ++ packedTail.2)

def ordered? : List Object → Bool
  | [] => true
  | object :: tail =>
      tail.all (fun later => decide (object.endOffset ≤ later.offset)) && ordered? tail

theorem packFrom_declarations (cursor : Nat) (declarations : List Declaration) :
    (packFrom cursor declarations).1.map Object.declaration = declarations := by
  induction declarations generalizing cursor with
  | nil => rfl
  | cons declaration tail ih =>
      simp only [packFrom, List.map_cons, List.cons.injEq, true_and]
      exact ih _

theorem packFrom_offsetsAligned (cursor : Nat) (declarations : List Declaration)
    (valid : ∀ declaration ∈ declarations, Nat.isPowerOfTwo declaration.alignment) :
    ∀ object ∈ (packFrom cursor declarations).1,
      object.offset % object.declaration.alignment = 0 := by
  induction declarations generalizing cursor with
  | nil => simp [packFrom]
  | cons declaration tail ih =>
      intro object member
      simp only [packFrom, List.mem_cons] at member
      rcases member with rfl | member
      · exact alignUp_mod_eq_zero _ (Nat.pos_of_isPowerOfTwo (valid _ List.mem_cons_self))
      · apply ih (alignUp cursor declaration.alignment + declaration.bytes.length)
          (fun later laterMember => valid later (List.mem_cons_of_mem declaration laterMember))
          object member

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
  if aligned : packed.1.all (fun object => decide
      (object.offset % object.declaration.alignment = 0)) = true then
    if ordered : ordered? packed.1 = true then
      if exact : packed.1.all (fun object => decide
          ((rawSection.contents.drop object.offset).take object.declaration.bytes.length =
            object.declaration.bytes)) = true then
        if contained : packed.1.all (fun object => decide
            (object.endOffset ≤ rawSection.contents.length)) = true then
          some ⟨packed.1, rawSection, rfl, packFrom_declarations 0 table.declarations,
            rfl, aligned, ordered, exact, contained⟩
        else none
      else none
    else none
  else none

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

private theorem find_object_of_mem {objects : List Object}
    (unique : (objects.map (fun object => object.declaration.name)).Nodup)
    {object : Object} (member : object ∈ objects) :
    objects.find? (fun candidate => candidate.declaration.name = object.declaration.name) =
      some object := by
  induction objects with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · have different : head.declaration.name ≠ object.declaration.name := by
          intro same
          exact unique.1 (List.mem_map.mpr ⟨object, member, same.symm⟩)
        rw [List.find?_cons_of_neg (by simpa using different)]
        exact ih unique.2 member

theorem Layout.lookup?_complete {table : Table} (layout : Layout table)
    {object : Object} (member : object ∈ layout.objects) :
    layout.lookup? object.declaration.name = some object :=
  find_object_of_mem layout.namesUnique member

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
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
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
