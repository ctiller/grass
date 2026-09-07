import Grass.Construct.Link.Raw

/-!
# Format-neutral raw link producer fixtures

Fixtures pin initialized/zero-fill extents, section-relative definitions,
relocations, external identities, entries, parameterized source provenance,
and structural rejection cases.
-/

namespace Grass.Tests.Construct.LinkRaw

open Grass Grass.Construct.Link Grass.Std.Logical

private inductive RelocKind where
  | pcRelative32
deriving Repr, DecidableEq

private structure ImportIdentity where
  provider : StableId
deriving Repr, DecidableEq

private structure SourceProvenance where
  block : StableId
  authoredIndex : Nat
deriving Repr, DecidableEq

private def fragmentId : LinkFragmentId := ⟨⟨"test.link", "fragment"⟩⟩
private def textId : SectionId := ⟨⟨"test.link", "text"⟩⟩
private def entryId : SymbolId := ⟨⟨"test.link", "entry"⟩⟩
private def importId : SymbolId := ⟨⟨"test.link", "write"⟩⟩
private def provenance : SourceProvenance := ⟨⟨"test.link", "block"⟩, 0⟩
private def bytes : Grass.Std.Logical.ByteArray :=
  Vec.fromList [0x90, 0xE8, 0x00, 0x00, 0x00, 0x00]
private def text : SectionContribution :=
  ⟨textId, 16, .code, ⟨true, false, true⟩, ⟨bytes, 2⟩⟩
private def entry : SymbolDefinition := ⟨entryId, textId, 0, .exported⟩
private def external : ExternalReference ImportIdentity :=
  ⟨importId, ⟨⟨"test.provider", "write"⟩⟩⟩
private def relocation : RelocationRequest RelocKind :=
  ⟨textId, 2, .pcRelative32, importId, 0⟩
private def mapped : SourceMapEntry SourceProvenance :=
  ⟨textId, 0, 6, provenance⟩
private def fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance :=
  ⟨fragmentId, [text], [entry], [relocation], [external], [entryId], [mapped]⟩

example : text.content.initializedSize = 6 := by decide
example : text.content.virtualSize = 8 := by decide
example : fragment.sectionIds = [textId] := by decide
example : fragment.definedSymbolIds = [entryId] := by decide
example : fragment.externalSymbolIds = [importId] := by decide
example : fragment.sourceMap.map SourceMapEntry.provenance = [provenance] := by decide
example : fragment.WellFormed := by decide
example : (checkRelocatableFragment fragment).isOk = true := by decide

private def dangling : RelocatableFragment RelocKind ImportIdentity SourceProvenance :=
  { fragment with relocations := [⟨textId, 2, .pcRelative32,
      ⟨⟨"test.link", "missing"⟩⟩, 0⟩] }
example : ¬dangling.WellFormed := by decide
example : (checkRelocatableFragment dangling).isOk = false := by decide

private def outOfBoundsMap :
    RelocatableFragment RelocKind ImportIdentity SourceProvenance :=
  { fragment with sourceMap := [⟨textId, 4, 4, provenance⟩] }
example : ¬outOfBoundsMap.WellFormed := by decide

private def duplicateSection :
    RelocatableFragment RelocKind ImportIdentity SourceProvenance :=
  { fragment with sections := [text, text] }
example : ¬duplicateSection.WellFormed := by decide

private def exactRelation
    (source : List Nat)
    (payload : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    Prop := source.length = payload.sourceMap.length
private def certified : CertifiedRelocatableFragment exactRelation [42] fragment :=
  ⟨⟨by decide⟩, rfl⟩
example : exactRelation [42] fragment := certified.exact

end Grass.Tests.Construct.LinkRaw
