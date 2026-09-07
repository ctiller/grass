import Grass.Construct.FrameVerified

namespace Grass.Tests.Construct.FrameVerified

open Grass Grass.Core Grass.CFG Grass.Construct Grass.Construct.Layout
  Grass.Construct.Fragment Grass.ISA.X86

private inductive Instruction where
  | push (r : Gpr) | pop (r : Gpr) | sub (n : Nat) | add (n : Nat)
  | spill (r : Gpr) (offset : Nat) | reload (r : Gpr) (offset : Nat)
deriving Repr, DecidableEq

private def sourceBackend : FrameSourceBackend Instruction where
  push := .push
  pop := .pop
  subtractRsp n := [.sub n]
  addRsp n := [.add n]
  spill r offset := [.spill r offset]
  reload r offset := [.reload r offset]

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

private def backend : FrameVerifiedBackend Instruction Unit Nat semantics effects where
  source := sourceBackend
  saveContract _ := contract
  restoreContract _ := contract
  enterContract _ := contract
  leaveContract _ := contract
  slotContract _ _ _ := contract
  saveVerified frame := verified (sourceBackend.save frame)
  restoreVerified frame := verified (sourceBackend.restore frame)
  enterVerified frame := verified (sourceBackend.enter frame)
  leaveVerified frame := verified (sourceBackend.leave frame)
  spillVerified _ slot register :=
    verified (.literal (sourceBackend.spill register slot.absoluteOffset))
  reloadVerified _ slot register :=
    verified (.literal (sourceBackend.reload register slot.absoluteOffset))
  saveSourceExact _ := rfl
  restoreSourceExact _ := rfl
  enterSourceExact _ := rfl
  leaveSourceExact _ := rfl
  spillSourceExact _ _ _ := rfl
  reloadSourceExact _ _ _ := rfl

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def object : StackObject profile := ⟨⟨"slot"⟩, ⟨8, 8⟩, 0, root⟩
private def layout : StackLayout profile :=
  ⟨[⟨root, none⟩], [object], 16, 16, 128⟩
private def plan : Win64FramePlan profile := ⟨layout, [.rbx], 0, 32, 48⟩
private def frame : CheckedWin64Frame profile := ⟨plan, by native_decide⟩
private def slot : FrameObjectRef frame := ⟨object, by simp [frame, plan, layout]⟩

example : (backend.save frame).source = sourceBackend.save frame :=
  backend.saveSourceExact frame
example : (backend.restore frame).source = sourceBackend.restore frame :=
  backend.restoreSourceExact frame
example : (backend.enter frame).source = sourceBackend.enter frame :=
  backend.enterSourceExact frame
example : (backend.leave frame).source = sourceBackend.leave frame :=
  backend.leaveSourceExact frame
example : (backend.spill frame slot .rax).source.expand = [.spill .rax 32] := by
  native_decide
example : (backend.reload frame slot .rax).source.expand = [.reload .rax 32] := by
  native_decide

end Grass.Tests.Construct.FrameVerified
