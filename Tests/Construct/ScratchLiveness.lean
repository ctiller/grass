import Grass.Construct.ScratchLiveness

/-!
# Scratch liveness bridge fixtures

Fixtures pin exact entry-liveness correspondence, selected-register
non-liveness, and source transparency through the liveness-checked binder.
-/

namespace Grass.Tests.Construct.ScratchLiveness

open Grass.CFG Grass.Construct Grass.Construct.Fragment

inductive Register where
  | r0 | r1 | r2
deriving Repr, DecidableEq

structure State where
  live : List Register
deriving Repr

private def request : ScratchRequest Register :=
  ⟨[.r0, .r1, .r2], [.r0, .r2]⟩
private def selection : CheckedScratch request :=
  ⟨.r1, by decide, by decide⟩
private def tag : ExitTag := ⟨⟨"test.scratch.live", "normal"⟩⟩
private def normalExit : ExitContract State := ⟨tag, fun _ => True⟩
private def contract : BlockContract State :=
  ⟨fun state => state.live = request.live, [normalExit]⟩
private def model : ScratchLivenessModel Register State :=
  ⟨fun state register => register ∈ state.live⟩
private def context : CheckedScratchContext model contract request where
  selection := selection
  liveExact := by
    intro state entry register
    change state.live = request.live at entry
    change register ∈ state.live ↔ register ∈ request.live
    rw [entry]

example {state : State} (entry : contract.requires state) :
    ¬model.Live state context.selection.register :=
  context.selectedNotLive entry

private def semantics : Semantics Register State :=
  ⟨fun _ _ _ => True⟩
private def effectModel : EffectModel Register (List Register) :=
  ⟨id⟩
private def body (handle : ScratchHandle context.selection) :
    VerifiedFragment semantics effectModel contract where
  source := .literal [handle.register]
  contractWellFormed := by decide
  effects := [handle.register]
  effectsExact := rfl
  localCorrect := by
    intro _ _ _ _
    exact ⟨normalExit, by simp [contract], trivial, by
      intro candidate member _
      simp [contract] at member
      subst candidate
      rfl⟩

example : (withLiveScratch context body).source.expand = [.r1] := by decide
example : (withLiveScratch context body).effects = [.r1] := by decide
example : (withLiveScratch context body).source =
    (body context.selection.handle).source :=
  withLiveScratch_source context body

end Grass.Tests.Construct.ScratchLiveness
