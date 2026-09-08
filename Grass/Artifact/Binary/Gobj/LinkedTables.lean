import Grass.Artifact.Binary.Gobj.Relocation

/-!
# Cross-table `.gobj` structural validation

`GobjLinkedTables` joins the independently framed section, symbol, and
relocation bodies only after their section-relative extents and table references
have been checked. Target-specific relocation-kind legality remains outside this
generic layer.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Grammar Grass.Std.Logical

/-- A symbol's section exists and contains its complete half-open extent. -/
def GobjSymbol.ValidForSections (entry : GobjSymbol)
    (sections : GobjSectionTable) : Prop :=
  match sections.entries.get? entry.sectionIndex.toNat with
  | some target =>
    entry.offset.toNat + entry.size.toNat ≤ target.contents.bytes.length
  | none => False

instance (entry : GobjSymbol) (sections : GobjSectionTable) :
    Decidable (entry.ValidForSections sections) := by
  unfold GobjSymbol.ValidForSections
  cases h : sections.entries.get? entry.sectionIndex.toNat with
  | none => infer_instance
  | some target => infer_instance

/-- Every symbol extent is contained in the section it names. -/
def GobjSymbolTable.ValidForSections (symbols : GobjSymbolTable)
    (sections : GobjSectionTable) : Prop :=
  ∀ entry ∈ symbols.entries.toList, entry.ValidForSections sections

instance (symbols : GobjSymbolTable) (sections : GobjSectionTable) :
    Decidable (symbols.ValidForSections sections) := by
  unfold GobjSymbolTable.ValidForSections
  infer_instance

/-- A relocation starts at an existing byte in the section it names. -/
def GobjRelocation.LocationValidFor (entry : GobjRelocation)
    (sections : GobjSectionTable) : Prop :=
  match sections.entries.get? entry.sectionIndex.toNat with
  | some target => entry.offset.toNat < target.contents.bytes.length
  | none => False

instance (entry : GobjRelocation) (sections : GobjSectionTable) :
    Decidable (entry.LocationValidFor sections) := by
  unfold GobjRelocation.LocationValidFor
  cases h : sections.entries.get? entry.sectionIndex.toNat with
  | none => infer_instance
  | some target => infer_instance

/-- Every relocation location is an existing byte of its named section. -/
def GobjRelocationTable.LocationsValidFor (relocations : GobjRelocationTable)
    (sections : GobjSectionTable) : Prop :=
  ∀ entry ∈ relocations.entries.toList, entry.LocationValidFor sections

instance (relocations : GobjRelocationTable) (sections : GobjSectionTable) :
    Decidable (relocations.LocationsValidFor sections) := by
  unfold GobjRelocationTable.LocationsValidFor
  infer_instance

/-- Three decoded tables with all generic cross-references validated. -/
structure GobjLinkedTables where
  sections : GobjSectionTable
  symbols : GobjSymbolTable
  relocations : GobjRelocationTable
  symbolExtentsValid : symbols.ValidForSections sections
  relocationReferencesValid : relocations.ValidFor sections symbols
  relocationLocationsValid : relocations.LocationsValidFor sections
deriving DecidableEq, Repr

/-- Decode and jointly validate the three structurally linked `.gobj` tables. -/
def parseGobjLinkedTables (payload : GobjPayload) :
    Except ParseError GobjLinkedTables :=
  match payload.parseSections with
  | .error error => .error error
  | .ok sections =>
    match payload.parseSymbols with
    | .error error => .error error
    | .ok symbols =>
      match payload.parseRelocations with
      | .error error => .error error
      | .ok relocations =>
        if symbolExtentsValid : symbols.ValidForSections sections then
          if relocationReferencesValid : relocations.ValidFor sections symbols then
            if relocationLocationsValid :
                relocations.LocationsValidFor sections then
              .ok {
                sections := sections
                symbols := symbols
                relocations := relocations
                symbolExtentsValid := symbolExtentsValid
                relocationReferencesValid := relocationReferencesValid
                relocationLocationsValid := relocationLocationsValid }
            else
              .error (.malformed ".gobj relocation location is out of bounds")
          else
            .error (.malformed ".gobj relocation table reference is out of bounds")
        else
          .error (.malformed ".gobj symbol extent is out of bounds")

/-- Replace the three linked raw bodies with canonical validated tables. -/
def GobjPayload.withLinkedTables (payload : GobjPayload)
    (tables : GobjLinkedTables)
    (sectionsFit : (writeGobjSectionTable tables.sections).length < 2 ^ 32)
    (symbolsFit : (writeGobjSymbolTable tables.symbols).length < 2 ^ 32)
    (relocationsFit :
      (writeGobjRelocationTable tables.relocations).length < 2 ^ 32) :
    GobjPayload :=
  ((payload.withSectionTable tables.sections sectionsFit).withSymbolTable
    tables.symbols symbolsFit).withRelocationTable
      tables.relocations relocationsFit

/-- `parseGobjLinkedTables_withLinkedTables` recovers every validated table. -/
@[simp] theorem parseGobjLinkedTables_withLinkedTables
    (payload : GobjPayload) (tables : GobjLinkedTables)
    (sectionsFit : (writeGobjSectionTable tables.sections).length < 2 ^ 32)
    (symbolsFit : (writeGobjSymbolTable tables.symbols).length < 2 ^ 32)
    (relocationsFit :
      (writeGobjRelocationTable tables.relocations).length < 2 ^ 32) :
    parseGobjLinkedTables
        (payload.withLinkedTables tables sectionsFit symbolsFit relocationsFit) =
      .ok tables := by
  have parsedSections :
      (payload.withLinkedTables tables sectionsFit symbolsFit
        relocationsFit).parseSections = .ok tables.sections := by
    unfold GobjPayload.withLinkedTables GobjPayload.withRelocationTable
      GobjPayload.withSymbolTable GobjPayload.parseSections
    exact parseGobjSectionTableBody_toFramed tables.sections sectionsFit
  have parsedSymbols :
      (payload.withLinkedTables tables sectionsFit symbolsFit
        relocationsFit).parseSymbols = .ok tables.symbols := by
    unfold GobjPayload.withLinkedTables GobjPayload.withRelocationTable
      GobjPayload.withSymbolTable GobjPayload.parseSymbols
    exact parseGobjSymbolTableBody_toFramed tables.symbols symbolsFit
  have parsedRelocations :
      (payload.withLinkedTables tables sectionsFit symbolsFit
        relocationsFit).parseRelocations = .ok tables.relocations := by
    unfold GobjPayload.withLinkedTables GobjPayload.parseRelocations
    exact parseGobjRelocationTableBody_toFramed tables.relocations
      relocationsFit
  unfold parseGobjLinkedTables
  rw [parsedSections, parsedSymbols, parsedRelocations]
  simp only
  rw [dif_pos tables.symbolExtentsValid]
  rw [dif_pos tables.relocationReferencesValid]
  rw [dif_pos tables.relocationLocationsValid]

end Grass.Artifact.Binary.Gobj
