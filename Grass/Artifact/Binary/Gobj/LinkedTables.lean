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

/-- Executable section-extent check for one symbol. -/
def GobjSymbol.isValidForSections (entry : GobjSymbol)
    (sections : GobjSectionTable) : Bool :=
  match entry.body with
  | .imported _ => true
  | .defined definition =>
    match sections.entries.get? definition.sectionIndex.toNat with
    | some target =>
      decide (definition.offset.toNat + definition.size.toNat ≤
        target.contents.bytes.length)
    | none => false

/-- A defined symbol's section contains its complete half-open extent. -/
def GobjSymbol.ValidForSections (entry : GobjSymbol)
    (sections : GobjSectionTable) : Prop :=
  entry.isValidForSections sections = true

instance (entry : GobjSymbol) (sections : GobjSectionTable) :
    Decidable (entry.ValidForSections sections) := by
  unfold GobjSymbol.ValidForSections
  infer_instance

/-- Every symbol extent is contained in the section it names. -/
def GobjSymbolTable.ValidForSections (symbols : GobjSymbolTable)
    (sections : GobjSectionTable) : Prop :=
  ∀ entry ∈ symbols.entries.toList, entry.ValidForSections sections

instance (symbols : GobjSymbolTable) (sections : GobjSectionTable) :
    Decidable (symbols.ValidForSections sections) := by
  unfold GobjSymbolTable.ValidForSections
  infer_instance

/-- Executable import-index and exact-local-target check for one symbol. -/
def GobjSymbol.isValidForImports (entry : GobjSymbol)
    (imports : GobjImportManifest) : Bool :=
  match entry.body with
  | .defined _ => true
  | .imported importIndex =>
    match imports.entries.get? importIndex.toNat with
    | some target => decide (entry.name = target.localTarget)
    | none => false

/-- An imported symbol selects an existing manifest entry with the same name. -/
def GobjSymbol.ValidForImports (entry : GobjSymbol)
    (imports : GobjImportManifest) : Prop :=
  entry.isValidForImports imports = true

instance (entry : GobjSymbol) (imports : GobjImportManifest) :
    Decidable (entry.ValidForImports imports) := by
  unfold GobjSymbol.ValidForImports
  infer_instance

/-- Every imported symbol exactly names an existing manifest entry. -/
def GobjSymbolTable.ValidForImports (symbols : GobjSymbolTable)
    (imports : GobjImportManifest) : Prop :=
  ∀ entry ∈ symbols.entries.toList, entry.ValidForImports imports

instance (symbols : GobjSymbolTable) (imports : GobjImportManifest) :
    Decidable (symbols.ValidForImports imports) := by
  unfold GobjSymbolTable.ValidForImports
  infer_instance

/-- Every manifest entry is used by at least one imported symbol. -/
def GobjImportManifest.AllUsedBy (imports : GobjImportManifest)
    (symbols : GobjSymbolTable) : Prop :=
  ∀ index, index < imports.entries.length →
    ∃ entry ∈ symbols.entries.toList,
      entry.body = .imported (BitVec.ofNat 32 index)

instance (imports : GobjImportManifest) (symbols : GobjSymbolTable) :
    Decidable (imports.AllUsedBy symbols) := by
  unfold GobjImportManifest.AllUsedBy
  infer_instance

/-- Executable structural location check for a relocation-bearing section. -/
def GobjRelocation.isLocationValidFor (entry : GobjRelocation)
    (sections : GobjSectionTable) : Bool :=
  match sections.entries.get? entry.sectionIndex.toNat with
  | some target =>
    match target.profile with
    | .noRelocations => false
    | .relocatable _ => decide (entry.offset.toNat < target.contents.bytes.length)
  | none => false

/-- A relocation starts at an existing byte in a relocation-bearing section. -/
def GobjRelocation.LocationValidFor (entry : GobjRelocation)
    (sections : GobjSectionTable) : Prop :=
  entry.isLocationValidFor sections = true

instance (entry : GobjRelocation) (sections : GobjSectionTable) :
    Decidable (entry.LocationValidFor sections) := by
  unfold GobjRelocation.LocationValidFor
  infer_instance

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
  imports : GobjImportManifest
  symbolExtentsValid : symbols.ValidForSections sections
  symbolImportsValid : symbols.ValidForImports imports
  allImportsUsed : imports.AllUsedBy symbols
  relocationIndicesValid : relocations.IndicesValid sections symbols
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
        match payload.parseImports with
        | .error error => .error error
        | .ok imports =>
          if symbolExtentsValid : symbols.ValidForSections sections then
          if symbolImportsValid : symbols.ValidForImports imports then
          if allImportsUsed : imports.AllUsedBy symbols then
          if relocationIndicesValid : relocations.IndicesValid sections symbols then
            if relocationLocationsValid :
                relocations.LocationsValidFor sections then
              .ok {
                sections := sections
                symbols := symbols
                relocations := relocations
                imports := imports
                symbolExtentsValid := symbolExtentsValid
                symbolImportsValid := symbolImportsValid
                allImportsUsed := allImportsUsed
                relocationIndicesValid := relocationIndicesValid
                relocationLocationsValid := relocationLocationsValid }
            else
              .error (.malformed ".gobj relocation location is out of bounds")
          else
            .error (.malformed ".gobj relocation table reference is out of bounds")
          else .error (.malformed ".gobj import manifest contains an orphan entry")
          else .error (.malformed ".gobj imported symbol does not match its manifest entry")
        else
          .error (.malformed ".gobj symbol extent is out of bounds")

/-- Replace the four linked raw bodies with canonical validated tables. -/
def GobjPayload.withLinkedTables (payload : GobjPayload)
    (tables : GobjLinkedTables)
    (sectionsFit : (writeGobjSectionTable tables.sections).length < 2 ^ 32)
    (symbolsFit : (writeGobjSymbolTable tables.symbols).length < 2 ^ 32)
    (relocationsFit :
      (writeGobjRelocationTable tables.relocations).length < 2 ^ 32)
    (importsFit : (writeGobjImportManifest tables.imports).length < 2 ^ 32) :
    GobjPayload :=
  (((payload.withSectionTable tables.sections sectionsFit).withSymbolTable
    tables.symbols symbolsFit).withRelocationTable
      tables.relocations relocationsFit).withImportManifest tables.imports importsFit

/-- `parseGobjLinkedTables_withLinkedTables` recovers every validated table. -/
@[simp] theorem parseGobjLinkedTables_withLinkedTables
    (payload : GobjPayload) (tables : GobjLinkedTables)
    (sectionsFit : (writeGobjSectionTable tables.sections).length < 2 ^ 32)
    (symbolsFit : (writeGobjSymbolTable tables.symbols).length < 2 ^ 32)
    (relocationsFit :
      (writeGobjRelocationTable tables.relocations).length < 2 ^ 32)
    (importsFit : (writeGobjImportManifest tables.imports).length < 2 ^ 32) :
    parseGobjLinkedTables
        (payload.withLinkedTables tables sectionsFit symbolsFit relocationsFit
          importsFit) =
      .ok tables := by
  have parsedSections :
      (payload.withLinkedTables tables sectionsFit symbolsFit
        relocationsFit importsFit).parseSections = .ok tables.sections := by
    unfold GobjPayload.withLinkedTables GobjPayload.withRelocationTable
      GobjPayload.withImportManifest GobjPayload.withSymbolTable
      GobjPayload.parseSections
    exact parseGobjSectionTableBody_toFramed tables.sections sectionsFit
  have parsedSymbols :
      (payload.withLinkedTables tables sectionsFit symbolsFit
        relocationsFit importsFit).parseSymbols = .ok tables.symbols := by
    unfold GobjPayload.withLinkedTables GobjPayload.withRelocationTable
      GobjPayload.withImportManifest GobjPayload.withSymbolTable
      GobjPayload.parseSymbols
    exact parseGobjSymbolTableBody_toFramed tables.symbols symbolsFit
  have parsedRelocations :
      (payload.withLinkedTables tables sectionsFit symbolsFit
        relocationsFit importsFit).parseRelocations = .ok tables.relocations := by
    unfold GobjPayload.withLinkedTables GobjPayload.withImportManifest
      GobjPayload.parseRelocations
    exact parseGobjRelocationTableBody_toFramed tables.relocations
      relocationsFit
  have parsedImports :
      (payload.withLinkedTables tables sectionsFit symbolsFit relocationsFit
        importsFit).parseImports = .ok tables.imports := by
    unfold GobjPayload.withLinkedTables
    exact GobjPayload.parseImports_withImportManifest _ tables.imports importsFit
  unfold parseGobjLinkedTables
  rw [parsedSections, parsedSymbols, parsedRelocations, parsedImports]
  simp only
  rw [dif_pos tables.symbolExtentsValid]
  rw [dif_pos tables.symbolImportsValid]
  rw [dif_pos tables.allImportsUsed]
  rw [dif_pos tables.relocationIndicesValid]
  rw [dif_pos tables.relocationLocationsValid]

end Grass.Artifact.Binary.Gobj
