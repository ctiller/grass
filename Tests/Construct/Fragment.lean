import Grass.Construct.Fragment.Compose
import Grass.Construct.Fragment.Generator

/-!
# Verified fragment fixtures

The fixtures instantiate the open hierarchy with a tiny additive instruction
family, prove exact generated expansion and effects, and prove unique exit
classification without trusting the generator itself.
-/

namespace Grass.Tests.Construct.Fragment

open Grass Grass.CFG Grass.Construct.Fragment

def exitTag (name : String) : ExitTag := ⟨⟨"test.fragment", name⟩⟩
def fragmentId (name : String) : FragmentId := ⟨⟨"test.fragment", name⟩⟩

inductive Instruction where
  | add (amount : Nat)
deriving Repr, DecidableEq

def evalInstruction : Instruction → Nat → Nat
  | .add amount, state => state + amount

def eval : List Instruction → Nat → Nat
  | [], state => state
  | instruction :: rest, state => eval rest (evalInstruction instruction state)

def semantics : Semantics Instruction Nat where
  Executes := fun instructions before after => eval instructions before = after

def effectOf : Instruction → Nat
  | .add amount => amount

def effects : EffectModel Instruction Nat where
  derive := fun instructions => (instructions.map effectOf).sum

theorem eval_append (left right : List Instruction) (state : Nat) :
    eval (left ++ right) state = eval right (eval left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, eval]
      exact ih (evalInstruction instruction state)

theorem effects_append (left right : List Instruction) :
    effects.derive (left ++ right) =
      effects.derive left + effects.derive right := by
  simp [effects]

def sequentialLaws : SequentialLaws semantics effects where
  combine := Nat.add
  executes_append := by
    intro left right before after
    constructor
    · intro h
      refine ⟨eval left before, rfl, ?_⟩
      simpa [semantics, eval_append] using h
    · rintro ⟨middle, hleft, hright⟩
      simp only [semantics] at hleft hright ⊢
      rw [eval_append, hleft, hright]
  effects_append := effects_append

def contract (amount : Nat) : BlockContract Nat where
  requires := fun state => state = 0
  exits := [⟨exitTag "normal", fun state => state = amount⟩]

def addFragment (amount : Nat) : VerifiedFragment semantics effects (contract amount) where
  source := .generated (fragmentId "add") (.literal [.add amount])
  contractWellFormed := by simp [contract, BlockContract.WellFormed,
    BlockContract.wellFormed, BlockContract.exitTags]
  effects := amount
  effectsExact := by simp [effects, effectOf]
  localCorrect := by
    intro before after hbefore hexec
    subst before
    simp [semantics, eval, evalInstruction] at hexec
    subst after
    refine ⟨⟨exitTag "normal", fun state => state = amount⟩, ?_, rfl, ?_⟩
    · simp [contract]
    · intro candidate hcandidate hholds
      simp [contract] at hcandidate
      subst candidate
      rfl

def generator : Generator Nat Instruction Nat Nat semantics effects where
  contract := contract
  generate := addFragment

example : generator.expand 7 = [.add 7] := by
  simp [generator, Generator.expand, addFragment]

example :
    (Source.generated (fragmentId "first")
      (.literal [Instruction.add 7])).expand =
    (Source.generated (fragmentId "second")
      (.literal [Instruction.add 7])).expand := by
  simp

example : (generator.generate 7).instructionCount = 1 := by
  simp [generator, VerifiedFragment.instructionCount, addFragment,
    Source.instructionCount]
example : (generator.generate 7).effects = effects.derive (generator.expand 7) :=
  Generator.generated_effects_exact generator 7

example : ClassifiesExactlyOneExit (contract 7) 7 := by
  apply (generator.generate 7).localCorrect 0 7 rfl
  simp [generator, addFragment, semantics, eval, evalInstruction]

def overlappingExits : BlockContract Nat where
  requires := fun _ => True
  exits := [
    ⟨exitTag "normal", fun _ => True⟩,
    ⟨exitTag "fault", fun _ => True⟩
  ]

example : ¬ ClassifiesExactlyOneExit overlappingExits 0 := by
  simp [ClassifiesExactlyOneExit, overlappingExits] <;> decide

def contractFrom (before amount : Nat) : BlockContract Nat where
  requires := fun state => state = before
  exits := [⟨exitTag "normal", fun state => state = before + amount⟩]

def addFrom (before amount : Nat) :
    VerifiedFragment semantics effects (contractFrom before amount) where
  source := .literal [.add amount]
  contractWellFormed := by
    simp [contractFrom, BlockContract.WellFormed, BlockContract.wellFormed,
      BlockContract.exitTags]
  effects := amount
  effectsExact := by simp [effects, effectOf]
  localCorrect := by
    intro initial after hinitial hexec
    subst initial
    simp [semantics, eval, evalInstruction] at hexec
    subst after
    refine ⟨⟨exitTag "normal", fun state => state = before + amount⟩,
      ?_, rfl, ?_⟩
    · simp [contractFrom]
    · intro candidate hcandidate hholds
      simp [contractFrom] at hcandidate
      subst candidate
      rfl

def first := addFrom 0 2
def second := addFrom 2 3
def wrongSecond := addFrom 3 1

theorem boundary : BoundaryCompatible (contractFrom 0 2) (contractFrom 2 3) := by
  intro state classified
  rcases classified with ⟨selected, hmem, hensures, _⟩
  simp [contractFrom] at hmem
  subst selected
  exact hensures

example : ¬ BoundaryCompatible (contractFrom 0 2) (contractFrom 3 1) := by
  intro claimed
  have firstExit : ClassifiesExactlyOneExit (contractFrom 0 2) 2 := by
    apply first.localCorrect 0 2 rfl
    rfl
  have impossible := claimed 2 firstExit
  simp [contractFrom] at impossible

def composed := first.compose sequentialLaws second boundary

example : composed.source.expand = [.add 2, .add 3] := by
  simp [composed, first, second, addFrom]

example : composed.effects = 5 := by
  simp [composed, VerifiedFragment.compose, sequentialLaws, first, second, addFrom]

example : ClassifiesExactlyOneExit (thenContract (contractFrom 0 2)
    (contractFrom 2 3)) 5 := by
  apply composed.localCorrect 0 5 rfl
  have hexpand : composed.source.expand =
      first.source.expand ++ second.source.expand := by
    exact VerifiedFragment.compose_source_expand sequentialLaws first second boundary
  rw [hexpand]
  simp [semantics, first, second, addFrom, eval, evalInstruction]

end Grass.Tests.Construct.Fragment
