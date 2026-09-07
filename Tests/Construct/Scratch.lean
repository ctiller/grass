import Grass.Construct.Scratch

/-!
# Generic scratch-selection fixtures

Fixtures pin authored-order selection, exact candidate and non-live evidence,
duplicate/no-available rejection, and source transparency of the checked binder.
-/

namespace Grass.Tests.Construct.Scratch

open Grass.CFG Grass.Construct Grass.Construct.Fragment

inductive Register where
  | r0 | r1 | r2
deriving Repr, DecidableEq

private def request : ScratchRequest Register :=
  ⟨[.r0, .r1, .r2], [.r0, .r2]⟩
private def checked : CheckedScratch request :=
  match checkScratch request with
  | .ok selected => selected
  | .error _ => ⟨.r1, by decide, by decide⟩

example : request.available? = some .r1 := by decide
example : checked.register = .r1 := by decide
example : checked.register ∈ request.candidates := checked.candidateMember
example : checked.register ∉ request.live := checked.notLive

private def duplicate : ScratchRequest Register :=
  ⟨[.r0, .r0], []⟩
example : checkScratch duplicate =
    .error (.duplicateCandidates [.r0, .r0]) := by rfl

private def exhausted : ScratchRequest Register :=
  ⟨[.r0, .r1], [.r0, .r1]⟩
example : checkScratch exhausted = .error .noAvailable := by rfl

private def tag : ExitTag := ⟨⟨"test.scratch", "normal"⟩⟩
private def normalExit : ExitContract Unit := ⟨tag, fun _ => True⟩
private def contract : BlockContract Unit :=
  ⟨fun _ => True, [normalExit]⟩
private def semantics : Semantics Register Unit :=
  ⟨fun _ _ _ => True⟩
private def effectModel : EffectModel Register (List Register) :=
  ⟨id⟩

private def body (handle : ScratchHandle checked) :
    VerifiedFragment semantics effectModel contract where
  source := .literal [handle.register]
  contractWellFormed := by decide
  effects := [handle.register]
  effectsExact := by rfl
  localCorrect := by
    intro _ _ _ _
    exact ⟨normalExit, by simp [contract], trivial, by
      intro candidate member _
      simp [contract] at member
      subst candidate
      rfl⟩

example : (withSelectedScratch checked body).source.expand = [.r1] := by decide
example : (withSelectedScratch checked body).effects = [.r1] := by decide
example : (withSelectedScratch checked body).source = (body checked.handle).source :=
  withSelectedScratch_source checked body

end Grass.Tests.Construct.Scratch
