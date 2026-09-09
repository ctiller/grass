import Grass.Artifact.Binary.Endian
import Grass.Artifact.PE.Layout

/-!
# PE32+ import-section construction

This module lays out import descriptors, address/lookup thunk arrays, hint/name
records, and library names for every requested `ImportLibrary`. All links are
derived RVAs into the generated `.idata` section.

Format authority: Microsoft, [PE Format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format),
sections "Import Directory Table", "Import Lookup Table", "Hint/Name Table",
and "Import Address Table"; retrieved 2026-09-01 in `docs/REFERENCES.md`.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical Grass.Artifact.Binary

/-- Bytes occupied by an import descriptor. -/
def importDescriptorSize : Nat := 20

/-- Descriptor-table extent, including its all-zero terminator. -/
def importDescriptorTableSize (libraryCount : Nat) : Nat :=
  importDescriptorSize * (libraryCount + 1)

/-- One 64-bit thunk per symbol and one zero terminator. -/
def thunkArraySize (symbolCount : Nat) : Nat := 8 * (symbolCount + 1)

/-- A serialized import name is nonempty and contains no embedded terminator. -/
def importNameValid (name : Std.Logical.ByteArray) : Bool :=
  decide (0 < name.length) && name.toList.all (fun byte => decide (byte ≠ 0))

/-- Every symbol in one library has a valid serialized name. -/
def importSymbolsValid : List ImportSymbol → Bool
  | [] => true
  | symbol :: tail => importNameValid symbol.name && importSymbolsValid tail

/-- Validate every library and require at least one symbol in each descriptor. -/
def importLibrariesValid : List ImportLibrary → Bool
  | [] => true
  | library :: tail =>
      importNameValid library.name && decide (0 < library.symbols.length) &&
        importSymbolsValid library.symbols.toList && importLibrariesValid tail

/-- Hint/name record with zero hint, NUL termination, and even-byte padding. -/
def writeHintName (symbol : ImportSymbol) : Std.Logical.ByteArray :=
  let body := writeLittleEndian (count := 2) (0 : BitVec 16) ++
    symbol.name ++ Vec.fromList [0]
  if body.length % 2 = 0 then body else body ++ Vec.fromList [0]

/-- Every generated hint/name record ends on an even boundary. -/
theorem writeHintName_length_even (symbol : ImportSymbol) :
    (writeHintName symbol).length % 2 = 0 := by
  let body := writeLittleEndian (count := 2) (0 : BitVec 16) ++
    symbol.name ++ Vec.fromList [0]
  change (if body.length % 2 = 0 then body else body ++ Vec.fromList [0]).length % 2 = 0
  split <;> rename_i parity
  · exact parity
  · simp only [Vec.length_append, Vec.length_fromList, List.length_cons,
      List.length_nil]
    omega

/-- Sum the exact generated hint/name extents. -/
def hintNamesSize : List ImportSymbol → Nat
  | [] => 0
  | symbol :: tail => (writeHintName symbol).length + hintNamesSize tail

/-- Running offsets for the hint/name records. -/
def hintNameOffsetsFrom (cursor : Nat) : List ImportSymbol → List Nat
  | [] => []
  | symbol :: tail =>
      cursor :: hintNameOffsetsFrom (cursor + (writeHintName symbol).length) tail

/-- Derived layout for one imported library inside `.idata`. -/
structure ImportLibraryLayout where
  library : ImportLibrary
  iatOffset : Nat
  iltOffset : Nat
  hintNameOffsets : Vec Nat
  dllNameOffset : Nat
  endOffset : Nat
deriving DecidableEq

/-- Lay out one library block from the next free section-relative offset. -/
def layoutImportLibraryAt (cursor : Nat) (library : ImportLibrary) :
    ImportLibraryLayout :=
  let iatOffset := alignUp cursor 8
  let iltOffset := iatOffset + thunkArraySize library.symbols.length
  let firstHint := iltOffset + thunkArraySize library.symbols.length
  let hintOffsets := hintNameOffsetsFrom firstHint library.symbols.toList
  let dllOffset := firstHint + hintNamesSize library.symbols.toList
  { library
    iatOffset
    iltOffset
    hintNameOffsets := Vec.fromList hintOffsets
    dllNameOffset := dllOffset
    endOffset := alignUp (dllOffset + library.name.length + 1) 8 }

/-- Lay out all library blocks after the complete descriptor table. -/
def layoutImportLibrariesFrom (cursor : Nat) : List ImportLibrary → List ImportLibraryLayout
  | [] => []
  | library :: tail =>
      let placed := layoutImportLibraryAt cursor library
      placed :: layoutImportLibrariesFrom placed.endOffset tail

/-- Complete import layout for a logical library vector. -/
def layoutImportLibraries (libraries : Vec ImportLibrary) : Vec ImportLibraryLayout :=
  Vec.fromList <| layoutImportLibrariesFrom
    (importDescriptorTableSize libraries.length) libraries.toList

/-- Serialize one twenty-byte import descriptor. -/
def writeImportDescriptor (baseRva : Nat) (layout : ImportLibraryLayout) :
    Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (BitVec.ofNat 32 (baseRva + layout.iltOffset)) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (0 : BitVec 32) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 (baseRva + layout.dllNameOffset)) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 (baseRva + layout.iatOffset))

/-- `writeImportDescriptor` emits exactly twenty bytes. -/
@[simp] theorem length_writeImportDescriptor (baseRva : Nat)
    (layout : ImportLibraryLayout) :
    (writeImportDescriptor baseRva layout).length = importDescriptorSize := by
  simp [writeImportDescriptor, importDescriptorSize]

/-- Serialize descriptors in layout order and append the zero terminator. -/
def writeImportDescriptors (baseRva : Nat) : List ImportLibraryLayout →
    Std.Logical.ByteArray
  | [] => Vec.replicate importDescriptorSize 0
  | layout :: tail =>
      writeImportDescriptor baseRva layout ++ writeImportDescriptors baseRva tail

/-- Serialize by-name thunks and their zero terminator. -/
def writeThunkArray (baseRva : Nat) : List Nat → Std.Logical.ByteArray
  | [] => writeLittleEndian (count := 8) (0 : BitVec 64)
  | offset :: tail =>
      writeLittleEndian (count := 8) (BitVec.ofNat 64 (baseRva + offset)) ++
        writeThunkArray baseRva tail

/-- Serialize hint/name records in source order. -/
def writeHintNames : List ImportSymbol → Std.Logical.ByteArray
  | [] => Vec.empty
  | symbol :: tail => writeHintName symbol ++ writeHintNames tail

/-- Serialize one complete library block, including trailing alignment padding. -/
def writeImportLibraryBlock (baseRva : Nat) (layout : ImportLibraryLayout) :
    Std.Logical.ByteArray :=
  let thunks := writeThunkArray baseRva layout.hintNameOffsets.toList
  let body := thunks ++ thunks ++ writeHintNames layout.library.symbols.toList ++
    layout.library.name ++ Vec.fromList [0]
  body ++ Vec.replicate (layout.endOffset - (layout.iatOffset + body.length)) 0

/-- Serialize aligned library blocks from a section-relative cursor. -/
def writeImportBodiesFrom (baseRva cursor : Nat) : List ImportLibraryLayout →
    Std.Logical.ByteArray
  | [] => Vec.empty
  | layout :: tail =>
      Vec.replicate (layout.iatOffset - cursor) 0 ++
      writeImportLibraryBlock baseRva layout ++
      writeImportBodiesFrom baseRva layout.endOffset tail

/-- Serialize a complete `.idata` payload for the supplied section RVA. -/
def writeImportSection (baseRva : Nat) (libraries : Vec ImportLibrary) :
    Std.Logical.ByteArray :=
  let layouts := layoutImportLibraries libraries
  let descriptors := writeImportDescriptors baseRva layouts.toList
  descriptors ++ writeImportBodiesFrom baseRva descriptors.length layouts.toList

/-- Thunk-array byte length is independent of the RVAs stored in its slots. -/
theorem length_writeThunkArray_independent (leftBase rightBase : Nat)
    (offsets : List Nat) :
    (writeThunkArray leftBase offsets).length =
      (writeThunkArray rightBase offsets).length := by
  induction offsets with
  | nil => simp [writeThunkArray]
  | cons offset tail ih => simp [writeThunkArray, ih]

/-- Descriptor-table byte length is independent of its stored RVAs. -/
theorem length_writeImportDescriptors_independent (leftBase rightBase : Nat)
    (layouts : List ImportLibraryLayout) :
    (writeImportDescriptors leftBase layouts).length =
      (writeImportDescriptors rightBase layouts).length := by
  induction layouts with
  | nil => rfl
  | cons layout tail ih => simp [writeImportDescriptors, ih]

/-- A library block changes addresses but not byte width when rebased. -/
theorem length_writeImportLibraryBlock_independent (leftBase rightBase : Nat)
    (layout : ImportLibraryLayout) :
    (writeImportLibraryBlock leftBase layout).length =
      (writeImportLibraryBlock rightBase layout).length := by
  unfold writeImportLibraryBlock
  simp only [Vec.length_append, Vec.length_replicate]
  have thunks := length_writeThunkArray_independent leftBase rightBase
    layout.hintNameOffsets.toList
  omega

/-- All aligned library bodies retain their width when rebased. -/
theorem length_writeImportBodiesFrom_independent (leftBase rightBase cursor : Nat)
    (layouts : List ImportLibraryLayout) :
    (writeImportBodiesFrom leftBase cursor layouts).length =
      (writeImportBodiesFrom rightBase cursor layouts).length := by
  induction layouts generalizing cursor with
  | nil => rfl
  | cons layout tail ih =>
      simp only [writeImportBodiesFrom, Vec.length_append, Vec.length_replicate]
      have block := length_writeImportLibraryBlock_independent leftBase rightBase layout
      have rest := ih layout.endOffset
      omega

/-- Rebasing an import section changes only address values, never its size. -/
theorem length_writeImportSection_independent_rva (leftBase rightBase : Nat)
    (libraries : Vec ImportLibrary) :
    (writeImportSection leftBase libraries).length =
      (writeImportSection rightBase libraries).length := by
  unfold writeImportSection
  simp only [Vec.length_append]
  let layouts := layoutImportLibraries libraries
  change
    (writeImportDescriptors leftBase layouts.toList).length +
        (writeImportBodiesFrom leftBase
          (writeImportDescriptors leftBase layouts.toList).length layouts.toList).length =
      (writeImportDescriptors rightBase layouts.toList).length +
        (writeImportBodiesFrom rightBase
          (writeImportDescriptors rightBase layouts.toList).length layouts.toList).length
  have descriptors := length_writeImportDescriptors_independent leftBase rightBase layouts.toList
  rw [descriptors]
  exact congrArg
    (fun n => (writeImportDescriptors rightBase layouts.toList).length + n)
    (length_writeImportBodiesFrom_independent leftBase rightBase
      (writeImportDescriptors rightBase layouts.toList).length layouts.toList)

/-- RVA of a caller-visible IAT slot. -/
def iatSlotRva (baseRva : Nat) (layout : ImportLibraryLayout) (symbolIndex : Nat) : Nat :=
  baseRva + layout.iatOffset + 8 * symbolIndex

/-- Canonical `.idata` short name. -/
def importSectionName : SectionName :=
  ⟨Vec.fromList [46, 105, 100, 97, 116, 97], by decide⟩

/-- Build a raw import section at its eventual RVA. -/
def makeImportSection (baseRva : Nat) (libraries : Vec ImportLibrary) : RawSection :=
  { name := importSectionName
    contents := writeImportSection baseRva libraries
    characteristics := 0xC0000040 }

/-- Last virtual start in an ordered placement list, or zero. -/
def lastVirtualStart : List PlacedSection → Nat
  | [] => 0
  | [placed] => placed.virtualSpan.start
  | _ :: tail => lastVirtualStart tail

/-- Append a provisional `.idata` section to discover its synthesized RVA. -/
private def withImportSection (description : ExecutableImageDescription)
    (baseRva : Nat) : ExecutableImageDescription :=
  { description with
    sections := description.sections ++
      Vec.fromList [makeImportSection baseRva description.imports] }

/-- Materialize requested imports as a final `.idata` raw section. The first
pass discovers its RVA; the second changes only same-sized address fields. -/
def materializeImports (description : ExecutableImageDescription) :
    ExecutableImageDescription :=
  if description.imports.length = 0 then description
  else
    let provisional := withImportSection description 0
    let baseRva := lastVirtualStart (placeImageSections provisional).toList
    withImportSection description baseRva

/-- Largest exclusive mapped section end; header extent is accounted separately. -/
def greatestVirtualEnd : List PlacedSection → Nat
  | [] => 0
  | placed :: tail => max placed.virtualSpan.endOffset (greatestVirtualEnd tail)

/-- Every section's exclusive end is included in `greatestVirtualEnd`. -/
theorem le_greatestVirtualEnd (sections : List PlacedSection) {placed : PlacedSection}
    (member : placed ∈ sections) : placed.virtualSpan.endOffset ≤ greatestVirtualEnd sections := by
  induction sections with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- Resolve a requested section-relative location against one placement. -/
def resolveSectionLocation? (placed : Vec PlacedSection)
    (location : SectionLocation) : Option Nat := do
  let placedSection ← placed.get? location.sectionIndex
  if location.offset < placedSection.source.contents.length then
    some (placedSection.virtualSpan.start + location.offset)
  else none

/-- A single resolved layout consumed by validation and serialization. All
absolute and relative addresses exposed to later stages are projections of this
value. -/
structure ImageLayout where
  requested : ExecutableImageDescription
  entryPointRequested : requested.entryPoint.sectionIndex < requested.sections.length
  materialized : ExecutableImageDescription
  materialized_eq : materialized = materializeImports requested
  placed : Vec PlacedSection
  placed_eq : placed = placeImageSections materialized
  entryPointRva : Nat
  entryPointRva_eq :
    resolveSectionLocation? placed requested.entryPoint = some entryPointRva
  sizeOfImage : Nat
  sizeOfImage_eq :
    sizeOfImage = alignUp
      (max (firstRawOffset canonicalPeOffset placed.length canonicalFileAlignment)
        (greatestVirtualEnd placed.toList)) canonicalSectionAlignment
  importSectionRva : Option Nat
  importSectionRva_eq : importSectionRva =
    if requested.imports.length = 0 then none
    else some (lastVirtualStart placed.toList)
  importLayouts : Vec ImportLibraryLayout
  importLayouts_eq : importLayouts = layoutImportLibraries requested.imports
deriving DecidableEq

/-- `ImageLayout.sectionsAfterHeaders` separates every section from the mapped
headers using this layout's actual materialized section count. -/
theorem ImageLayout.sectionsAfterHeaders (layout : ImageLayout)
    {placedSection : PlacedSection} (member : placedSection ∈ layout.placed.toList) :
    firstRawOffset canonicalPeOffset layout.placed.length canonicalFileAlignment ≤
      placedSection.virtualSpan.start := by
  rw [layout.placed_eq] at member ⊢
  rw [placeImageSections_length]
  exact placeImageSections_headers_before layout.materialized member

/-- `ImageLayout.headersWithinImage` includes all padded header bytes in the
declared mapped image extent, independently of whether any section is nonempty. -/
theorem ImageLayout.headersWithinImage (layout : ImageLayout) :
    firstRawOffset canonicalPeOffset layout.placed.length canonicalFileAlignment ≤
      layout.sizeOfImage := by
  rw [layout.sizeOfImage_eq]
  exact Nat.le_trans (Nat.le_max_left _ _) (le_alignUp _ _)

/-- `ImageLayout.sectionsWithinImage` includes every section's exclusive mapped
end in the same derived image extent. -/
theorem ImageLayout.sectionsWithinImage (layout : ImageLayout)
    {placedSection : PlacedSection} (member : placedSection ∈ layout.placed.toList) :
    placedSection.virtualSpan.endOffset ≤ layout.sizeOfImage := by
  rw [layout.sizeOfImage_eq]
  exact Nat.le_trans (le_greatestVirtualEnd _ member)
    (Nat.le_trans (Nat.le_max_right _ _) (le_alignUp _ _))

/-- Materialize imports once, place the resulting sections once, and resolve all
consumer-visible addresses from that placement. -/
def resolveImageLayout? (description : ExecutableImageDescription) : Option ImageLayout :=
  if entryRequested : description.entryPoint.sectionIndex < description.sections.length then
    let materialized := materializeImports description
    let placed := placeImageSections materialized
    match resolved : resolveSectionLocation? placed description.entryPoint with
    | none => none
    | some entryPointRva =>
        let importSectionRva :=
          if description.imports.length = 0 then none
          else some (lastVirtualStart placed.toList)
        some {
          requested := description
          entryPointRequested := entryRequested
          materialized
          materialized_eq := rfl
          placed
          placed_eq := rfl
          entryPointRva
          entryPointRva_eq := resolved
          sizeOfImage := alignUp
            (max (firstRawOffset canonicalPeOffset placed.length canonicalFileAlignment)
              (greatestVirtualEnd placed.toList)) canonicalSectionAlignment
          sizeOfImage_eq := rfl
          importSectionRva
          importSectionRva_eq := rfl
          importLayouts := layoutImportLibraries description.imports
          importLayouts_eq := rfl }
  else none

/-- Query an IAT slot from the same resolved placement used by the writer. -/
def ImageLayout.importAddressRva? (layout : ImageLayout)
    (libraryIndex symbolIndex : Nat) : Option Nat := do
  let baseRva ← layout.importSectionRva
  let library ← layout.importLayouts.get? libraryIndex
  let _symbol ← library.library.symbols.get? symbolIndex
  some (iatSlotRva baseRva library symbolIndex)

/-- Exception-directory coordinates from the requested table and this placement.
The production plan separately requires complete exception-table validation. -/
def ImageLayout.exceptionDirectory (layout : ImageLayout) : Nat × Nat :=
  match layout.requested.exceptionTable with
  | none => (0, 0)
  | some description =>
      ((resolveSectionLocation? layout.placed description.table.location).getD 0,
        description.table.size)

/-- `ImageLayout.ImportsResolved` states that materialized import bytes use the
`.idata` RVA from this exact final placement, rather than a provisional RVA. -/
def ImageLayout.ImportsResolved (layout : ImageLayout) : Prop :=
  if layout.requested.imports.length = 0 then
    layout.materialized = layout.requested ∧ layout.importSectionRva = none
  else
    ∃ baseRva, layout.importSectionRva = some baseRva ∧
      layout.materialized = withImportSection layout.requested baseRva

instance (layout : ImageLayout) : Decidable layout.ImportsResolved := by
  unfold ImageLayout.ImportsResolved
  infer_instance

end Grass.Artifact.PE
