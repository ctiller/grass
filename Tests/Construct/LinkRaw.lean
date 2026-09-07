import Grass.Construct.Link.Raw

/-!
# Format-neutral raw link producer fixtures

Fixtures pin initialized/zero-fill extents, section-relative definitions,
relocations, external identities, entries, source maps, and rejection cases.
-/

namespace Grass.Tests.Construct.LinkRaw

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Link
  Grass.Std.Logical

private inductive RelocKind where
  | pcRelative32
deriving Repr, DecidableEq

private structure ImportIdentity where
  provider : StableId
deriving Repr, DecidableEq

private def fragmentId : LinkFragmentId := ⟨⟨"test.link", "fragment"⟩⟩
private def textId : SectionId := ⟨⟨"test.link", "text"⟩⟩
private def entryId : SymbolId := ⟨⟨"test.link", "entry"⟩⟩
private def importId : SymbolId := ⟨⟨"test.link", "write"⟩⟩
private def blockId : BlockId := ⟨⟨"test.link", "block"⟩⟩
private def origin : SourceOrigin := ⟨[], [], 0⟩
private def bytes : Grass.Std.Logical.ByteArray :=
  Vec.fromList [0x90, 0xE8, 0x00, 0x00, 0x00, 0x00]
private def text : SectionContribution :=
  ⟨textId, 16, .code, ⟨true, false, true⟩, ⟨bytes, 2⟩⟩
private def entry : SymbolDefinition := ⟨entryId, textId, 0, .exported⟩
private def external : ExternalReference ImportIdentity :=
  ⟨importId, ⟨⟨"test.provider", "write"⟩⟩⟩
private def relocation : RelocationRequest RelocKind :=
  ⟨textId, 2, .pcRelative32, importId, 0⟩
private def mapped : SourceMapEntry := ⟨textId, 0, 6, blockId, origin⟩
private def fragment : RelocatableFragment RelocKind ImportIdentity :=
  ⟨fragmentId, [text], [entry], [relocation], [external], [entryId], [mapped]⟩

example : text.content.initializedSize = 6 := by decide
example : text.content.virtualSize = 8 := by decide
example : fragment.sectionIds = [textId] := by decide
example : fragment.definedSymbolIds = [entryId] := by decide
example : fragment.externalSymbolIds = [importId] := by decide
example : fragment.WellFormed := by native_decide
example : (checkRelocatableFragment fragment).isOk = true := by native_decide

private def dangling : RelocatableFragment RelocKind ImportIdentity :=
  { fragment with relocations := [⟨textId, 2, .pcRelative32,
      ⟨⟨"test.link", "missing"⟩⟩, 0⟩] }
example : ¬dangling.WellFormed := by native_decide
example : (checkRelocatableFragment dangling).isOk = false := by native_decide

private def outOfBoundsMap : RelocatableFragment RelocKind ImportIdentity :=
  { fragment with sourceMap := [⟨textId, 4, 4, blockId, origin⟩] }
example : ¬outOfBoundsMap.WellFormed := by native_decide

private def duplicateSection : RelocatableFragment RelocKind ImportIdentity :=
  { fragment with sections := [text, text] }
example : ¬duplicateSection.WellFormed := by native_decide

private def exactRelation
    (source : List Nat) (payload : RelocatableFragment RelocKind ImportIdentity) :
    Prop := source.length = payload.sourceMap.length
private def certified : CertifiedRelocatableFragment exactRelation [42] fragment :=
  ⟨⟨by native_decide⟩, rfl⟩
example : exactRelation [42] fragment := certified.exact

end Grass.Tests.Construct.LinkRaw
