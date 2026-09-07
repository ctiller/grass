import Grass.Construct.FrameStackObjectVerified

namespace Grass.Tests.Construct.FrameStackObjectVerified

open Grass.Core Grass.Memory Grass.CFG Grass.Construct Grass.Construct.Layout
  Grass.Construct.Fragment Grass.ISA.X86

private inductive Operand where | register (name : String)
deriving Repr, DecidableEq
private inductive Instruction where
  | load (range : ByteRange) (destination : Operand)
  | store (range : ByteRange) (source : Operand)
deriving Repr, DecidableEq

private def sourceBackend : StackObjectSourceBackend Instruction Operand where
  loadAt range destination := [.load range destination]
  storeAt range source := [.store range source]
private def semantics : Semantics Instruction Unit := ⟨fun _ _ _ => False⟩
private def effects : EffectModel Instruction Nat := ⟨List.length⟩
private def contract : BlockContract Unit := ⟨fun _ => True, []⟩
private def verified (source : Source Instruction) :
    VerifiedFragment semantics effects contract where
  source := source
  contractWellFormed := by simp [contract, BlockContract.WellFormed,
    BlockContract.wellFormed, BlockContract.exitTags]
  effects := source.expand.length
  effectsExact := rfl
  localCorrect := by intros; contradiction

private def backend :
    FrameStackObjectVerifiedBackend Instruction Operand Unit Nat semantics effects where
  source := sourceBackend
  loadContract _ _ _ _ := contract
  storeContract _ _ _ _ := contract
  loadVerified frame _ slice destination :=
    verified (sourceBackend.loadFrame frame slice destination)
  storeVerified frame _ slice source :=
    verified (sourceBackend.storeFrame frame slice source)
  loadSourceExact _ _ _ _ := rfl
  storeSourceExact _ _ _ _ := rfl

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def word : Layout.StackObject profile := ⟨⟨"word"⟩, ⟨8, 8⟩, 0, root⟩
private def layout : StackLayout profile := ⟨[⟨root, none⟩], [word], 16, 16, 64⟩
private def plan : Win64FramePlan profile := ⟨layout, [.rbx], 16, 32, 64⟩
private def frame : CheckedWin64Frame profile := ⟨plan, by decide⟩
private def slot : StackObjectRef frame.checkedLayout := ⟨word, by decide⟩
private def slice : CheckedStackSlice slot := ⟨⟨2, 4⟩, by decide⟩
private def destination : Operand := .register "rax"
private def source : Operand := .register "rbx"

example : (backend.load frame slice destination).source =
    sourceBackend.loadFrame frame slice destination := backend.loadSourceExact _ _ _
example : (backend.store frame slice source).source =
    sourceBackend.storeFrame frame slice source := backend.storeSourceExact _ _ _
example : (backend.load frame slice destination).source.expand =
    [.load ⟨50, 4⟩ destination] := by decide
example : (backend.store frame slice source).source.expand =
    [.store ⟨50, 4⟩ source] := by decide

end Grass.Tests.Construct.FrameStackObjectVerified
