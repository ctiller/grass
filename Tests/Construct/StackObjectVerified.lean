import Grass.Construct.StackObjectVerified

/-!
# Proof-bearing checked stack-object fixtures

Fixtures pin exact source preservation through direct and nominal verified
load/store projections.
-/

namespace Grass.Tests.Construct.StackObjectVerified

open Grass.Core Grass.Memory Grass.CFG Grass.Construct Grass.Construct.Layout
  Grass.Construct.Fragment

private inductive Operand where
  | register (name : String)
deriving Repr, DecidableEq

private inductive Instruction where
  | load (range : ByteRange) (destination : Operand)
  | store (range : ByteRange) (source : Operand)
deriving Repr, DecidableEq

private def sourceBackend : StackObjectSourceBackend Instruction Operand where
  loadAt range destination := [.load range destination]
  storeAt range source := [.store range source]

private def semantics : Semantics Instruction Unit :=
  ⟨fun _ _ _ => False⟩

private def effects : EffectModel Instruction Nat :=
  ⟨fun instructions => instructions.length⟩

private def contract : BlockContract Unit := ⟨fun _ => True, []⟩

private def verified (source : Source Instruction) :
    VerifiedFragment semantics effects contract where
  source := source
  contractWellFormed := by simp [contract, BlockContract.WellFormed,
    BlockContract.wellFormed, BlockContract.exitTags]
  effects := source.expand.length
  effectsExact := rfl
  localCorrect := by
    intro _ _ _ impossible
    exact False.elim impossible

private def backend :
    StackObjectVerifiedBackend Instruction Operand Unit Nat semantics effects where
  source := sourceBackend
  loadContract _ _ := contract
  storeContract _ _ := contract
  loadVerified slice destination := verified (sourceBackend.load slice destination)
  storeVerified slice source := verified (sourceBackend.store slice source)
  loadSourceExact _ _ := rfl
  storeSourceExact _ _ := rfl

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def word : Layout.StackObject profile :=
  ⟨⟨"word"⟩, ⟨8, 8⟩, 16, root⟩
private def layout : StackLayout profile :=
  ⟨[⟨root, none⟩], [word], 32, 16, 64⟩
private def checked : CheckedStackLayout profile := ⟨layout, by decide⟩
private def slot : StackObjectRef checked := ⟨word, by decide⟩
private def slice : CheckedStackSlice slot := ⟨⟨2, 4⟩, by decide⟩
private def destination : Operand := .register "rax"
private def source : Operand := .register "rbx"
private def namedRef : CheckedStackLayout.NamedStackObjectRef checked ⟨"word"⟩ :=
  ⟨slot, rfl⟩
private def named : NamedCheckedStackSlice checked ⟨"word"⟩ :=
  ⟨namedRef, slice⟩

example : (backend.load slice destination).source.expand =
    [.load ⟨18, 4⟩ destination] := by decide
example : (backend.store slice source).source.expand =
    [.store ⟨18, 4⟩ source] := by decide
example : (backend.loadNamed named destination).source =
    sourceBackend.loadNamed named destination := backend.loadSourceExact _ _
example : (backend.storeNamed named source).source =
    sourceBackend.storeNamed named source := backend.storeSourceExact _ _

end Grass.Tests.Construct.StackObjectVerified
