import Grass.Core.Identifiers
import Grass.Std.Logical.Vec

/-!
# Format-neutral raw link producer schema

`RelocatableFragment` is the construction-owned value consumed by artifact
serialization and linking. It records section-relative bytes, zero fill,
requested permissions, definitions, external identities, symbolic relocation
requests, entry candidates, and exact source-map ranges. It contains no `.gobj`,
COFF, PE, RVA, file-offset, or container-specific policy.

Relocation meaning, import identity, and source provenance are parameters
supplied by ISA/ABI, platform, and authored-source facets. The raw link seam
therefore depends only on stable core identities and logical bytes.
`CertifiedRelocatableFragment` separately pairs a structurally checked value
with the exact source-to-payload relation supplied by its backend.
-/

namespace Grass.Construct.Link

open Grass Grass.Std.Logical

universe u v w x

/-- Stable identity of one format-neutral section contribution. -/
structure SectionId where
  id : StableId
deriving Repr, DecidableEq, Hashable

/-- Stable identity of one defined or externally resolved symbol. -/
structure SymbolId where
  id : StableId
deriving Repr, DecidableEq, Hashable

/-- Stable identity of one independently produced relocatable fragment. -/
structure LinkFragmentId where
  id : StableId
deriving Repr, DecidableEq, Hashable

/-- Format-neutral section class requested by construction. -/
inductive SectionClass where
  | code
  | readOnlyData
  | writableData
  | unwind
  | custom (id : StableId)
deriving Repr, DecidableEq

/-- Requested final access policy, interpreted by the artifact format. -/
structure SectionPermissions where
  readable : Bool
  writable : Bool
  executable : Bool
deriving Repr, DecidableEq

/-- Initialized logical bytes followed by virtual zero fill. -/
structure SectionContent where
  initialized : Grass.Std.Logical.ByteArray
  zeroFill : Nat
deriving Repr, DecidableEq

namespace SectionContent

/-- Number of serialized initialized bytes contributed by this section. -/
def initializedSize (content : SectionContent) : Nat := content.initialized.length

/-- Total in-memory extent requested before final artifact placement. -/
def virtualSize (content : SectionContent) : Nat :=
  content.initializedSize + content.zeroFill

end SectionContent

/-- One format-neutral section contribution before final link placement. -/
structure SectionContribution where
  id : SectionId
  alignment : Nat
  class_ : SectionClass
  permissions : SectionPermissions
  content : SectionContent
deriving Repr, DecidableEq

/-- Visibility of one producer-defined symbol. -/
inductive SymbolVisibility where
  | local
  | exported
deriving Repr, DecidableEq

/-- One symbol defined at a section-relative virtual offset. -/
structure SymbolDefinition where
  symbol : SymbolId
  sectionId : SectionId
  offset : Nat
  visibility : SymbolVisibility
deriving Repr, DecidableEq

/-- One symbolic patch request at an initialized section-relative offset. -/
structure RelocationRequest (RelocKind : Type u) where
  sectionId : SectionId
  offset : Nat
  kind : RelocKind
  target : SymbolId
  addend : Int
deriving Repr, DecidableEq

/-- One unresolved symbol tied to an exact platform import identity. -/
structure ExternalReference (ImportIdentity : Type v) where
  symbol : SymbolId
  importIdentity : ImportIdentity
deriving Repr, DecidableEq

/-- Exact producer-defined provenance for a range of initialized section bytes. -/
structure SourceMapEntry (SourceProvenance : Type w) where
  sectionId : SectionId
  offset : Nat
  length : Nat
  provenance : SourceProvenance
deriving Repr, DecidableEq

/-- Complete format-neutral output of one construction/encoding producer. -/
structure RelocatableFragment (RelocKind : Type u) (ImportIdentity : Type v)
    (SourceProvenance : Type w) where
  id : LinkFragmentId
  sections : List SectionContribution
  definitions : List SymbolDefinition
  relocations : List (RelocationRequest RelocKind)
  externals : List (ExternalReference ImportIdentity)
  entryCandidates : List SymbolId
  sourceMap : List (SourceMapEntry SourceProvenance)
deriving Repr, DecidableEq

namespace RelocatableFragment

variable {RelocKind : Type u} {ImportIdentity : Type v} {SourceProvenance : Type w}

/-- Section identities in exact producer order. -/
def sectionIds
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    List SectionId :=
  fragment.sections.map SectionContribution.id

/-- Defined symbol identities in exact producer order. -/
def definedSymbolIds
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    List SymbolId :=
  fragment.definitions.map SymbolDefinition.symbol

/-- External symbol identities in exact producer order. -/
def externalSymbolIds
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    List SymbolId :=
  fragment.externals.map ExternalReference.symbol

/-- Find one exact section contribution by stable identity. -/
def findSection?
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance)
    (id : SectionId) : Option SectionContribution :=
  fragment.sections.find? fun contribution => contribution.id == id

/-- Whether a symbol is defined or externally resolved by this fragment. -/
def hasSymbol
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance)
    (symbol : SymbolId) : Bool :=
  fragment.definedSymbolIds.contains symbol ||
    fragment.externalSymbolIds.contains symbol

/-- Format-neutral structural validity before serialization or final linking. -/
def WellFormed
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    Prop :=
  fragment.sectionIds.Nodup ∧
  fragment.definedSymbolIds.Nodup ∧
  fragment.externalSymbolIds.Nodup ∧
  (∀ symbol ∈ fragment.definedSymbolIds,
    symbol ∉ fragment.externalSymbolIds) ∧
  (∀ contribution ∈ fragment.sections, 0 < contribution.alignment) ∧
  (∀ definition ∈ fragment.definitions,
    ∃ contribution,
      fragment.findSection? definition.sectionId = some contribution ∧
      definition.offset ≤ contribution.content.virtualSize) ∧
  (∀ relocation ∈ fragment.relocations,
    ∃ contribution,
      fragment.findSection? relocation.sectionId = some contribution ∧
      relocation.offset < contribution.content.initializedSize ∧
      fragment.hasSymbol relocation.target) ∧
  fragment.entryCandidates.Nodup ∧
  (∀ entry ∈ fragment.entryCandidates, entry ∈ fragment.definedSymbolIds) ∧
  (∀ mapped ∈ fragment.sourceMap,
    0 < mapped.length ∧
    ∃ contribution,
      fragment.findSection? mapped.sectionId = some contribution ∧
      mapped.offset + mapped.length ≤ contribution.content.initializedSize)

instance
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    Decidable fragment.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Executable structural validation of a producer fragment. -/
def wellFormed
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    Bool := decide fragment.WellFormed

@[simp] theorem wellFormed_iff
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    fragment.wellFormed ↔ fragment.WellFormed := by
  simp [wellFormed]

end RelocatableFragment

/-- Checked format-neutral producer value; no artifact bytes are emitted here. -/
structure CheckedRelocatableFragment {RelocKind : Type u}
    {ImportIdentity : Type v} {SourceProvenance : Type w}
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    Type (max u v w) where
  valid : fragment.WellFormed

/-- Structured rejection retaining the producer identity. -/
structure RawLinkError where
  fragment : LinkFragmentId
deriving Repr, DecidableEq

/-- Validate a format-neutral producer value before artifact consumption. -/
def checkRelocatableFragment {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    Except RawLinkError (CheckedRelocatableFragment fragment) :=
  if valid : fragment.WellFormed then .ok ⟨valid⟩
  else .error ⟨fragment.id⟩

/--
Structurally checked producer output tied to a backend-supplied exactness relation.

The relation is supplied by the selected construction/encoding backend; this
generic junction neither invents instruction semantics nor treats structural
validity as proof that bytes encode a source.
-/
structure CertifiedRelocatableFragment
    {Source : Type x} {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    (Exact : Source → RelocatableFragment RelocKind ImportIdentity
      SourceProvenance → Prop)
    (source : Source)
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) where
  checked : CheckedRelocatableFragment fragment
  exact : Exact source fragment

end Grass.Construct.Link
