import Grass.Construct.Fragment.Registry

/-!
# Explicit constructor-closure fixtures

The fixtures select two constructors with different parameter types from one
finite supplied value, reject ambiguity and absence, and pin exact verified
expansion through the selected constructor.
-/

namespace Grass.Tests.Construct.FragmentRegistry

open Grass Grass.CFG Grass.Construct.Fragment

private inductive Instruction where
  | emit (value : Nat)
deriving Repr, DecidableEq

private def semantics : Semantics Instruction Unit where
  Executes := fun _ _ _ => True

private def effects : EffectModel Instruction Nat where
  derive := List.length

private def exitTag : ExitTag := ⟨⟨"test.registry", "normal"⟩⟩

private def contract (_ : Nat) : BlockContract Unit where
  requires := fun _ => True
  exits := [⟨exitTag, fun _ => True⟩]

private def generated (value : Nat) : VerifiedFragment semantics effects (contract value) where
  source := .literal [.emit value]
  contractWellFormed := by
    simp [contract, BlockContract.WellFormed, BlockContract.wellFormed,
      BlockContract.exitTags]
  effects := 1
  effectsExact := rfl
  localCorrect := by
    intro _ _ _ _
    refine ⟨⟨exitTag, fun _ => True⟩, by simp [contract], trivial, ?_⟩
    intro candidate hcandidate _
    simp [contract] at hcandidate
    subst candidate
    rfl

private def natGenerator : Generator Nat Instruction Unit Nat semantics effects where
  contract := contract
  generate := generated

private def boolGenerator : Generator Bool Instruction Unit Nat semantics effects where
  contract := fun enabled => contract (if enabled then 1 else 0)
  generate := fun enabled => generated (if enabled then 1 else 0)

private def natId : FragmentId := ⟨⟨"test.registry", "nat"⟩⟩
private def boolId : FragmentId := ⟨⟨"test.registry", "bool"⟩⟩
private def missingId : FragmentId := ⟨⟨"test.registry", "missing"⟩⟩

private def natConstructor : Constructor Instruction Unit Nat semantics effects where
  id := natId
  Parameter := Nat
  generator := natGenerator

private def boolConstructor : Constructor Instruction Unit Nat semantics effects where
  id := boolId
  Parameter := Bool
  generator := boolGenerator

private def closure : ConstructorClosure Instruction Unit Nat semantics effects :=
  ⟨[natConstructor, boolConstructor]⟩

private def checked : CheckedConstructorClosure closure := ⟨by decide⟩
private def selected : SelectedConstructor closure checked natId :=
  ⟨natConstructor, rfl⟩
private def application : ConstructorApplication selected := by
  refine ⟨?_⟩
  change Nat
  exact 7
private def boolSelected : SelectedConstructor closure checked boolId :=
  ⟨boolConstructor, rfl⟩
private def boolApplication : ConstructorApplication boolSelected := by
  refine ⟨?_⟩
  change Bool
  exact true

example : closure.ids = [natId, boolId] := rfl
example : closure.WellFormed := by decide
example : selected.constructor.id = natId := selected.id_exact
example : selected.constructor ∈ closure.constructors := selected.member
example : application.source.expand = [.emit 7] := rfl
example : application.verified.source.expand = [.emit 7] := rfl
example : application.verified.source.expandLocated =
    [⟨⟨[natId], [], 0⟩, .emit 7⟩] := rfl
example : application.verified.effects = effects.derive [.emit 7] := rfl
example : boolApplication.verified.source.expand = [.emit 1] := rfl
example : (checked.select? natId).isSome = true := rfl
example : (checked.select? boolId).isSome = true := rfl
example : (checked.select? missingId).isNone = true := rfl
example : (checked.select natId).isOk = true := rfl
example : (checked.select missingId).isOk = false := rfl
example : checked.select missingId =
    .error ⟨missingId, [natId, boolId]⟩ := rfl

private def duplicate : ConstructorClosure Instruction Unit Nat semantics effects :=
  ⟨[natConstructor, natConstructor]⟩

example : ¬duplicate.WellFormed := by decide
example : (checkConstructorClosure duplicate).isOk = false := by decide

end Grass.Tests.Construct.FragmentRegistry
