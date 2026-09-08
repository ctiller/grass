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

def effects : EffectModel Instruction Nat where
  derive := fun instructions => instructions.foldl (fun total instruction =>
    match instruction with | .add amount => total + amount) 0

def contract (amount : Nat) : BlockContract Nat where
  requires := fun state => state = 0
  exits := [⟨exitTag "normal", fun state => state = amount⟩]

def addFragment (amount : Nat) : VerifiedFragment semantics effects (contract amount) where
  source := .generated (fragmentId "add") (.literal [.add amount])
  contractWellFormed := by simp [contract, BlockContract.WellFormed,
    BlockContract.wellFormed, BlockContract.exitTags]
  effects := amount
  effectsExact := by simp [effects]
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

example : (Source.sequence [
    Source.literal [Instruction.add 1],
    Source.generated (fragmentId "nested")
      (.literal [Instruction.add 2, Instruction.add 3])
  ]).leafCount = 2 := by simp

example :
    (Source.generated (fragmentId "first")
      (.literal [Instruction.add 7])).expand =
    (Source.generated (fragmentId "second")
      (.literal [Instruction.add 7])).expand := by
  simp

def locatedSource : Source Instruction :=
  .generated (fragmentId "outer") (.sequence [
    .literal [.add 1, .add 2],
    .generated (fragmentId "inner") (.literal [.add 3])
  ])

example : locatedSource.expandLocated = [
    ⟨⟨[fragmentId "outer"], [0], 0⟩, .add 1⟩,
    ⟨⟨[fragmentId "outer"], [0], 1⟩, .add 2⟩,
    ⟨⟨[fragmentId "outer", fragmentId "inner"], [1, 0], 0⟩, .add 3⟩
  ] := by decide

example : locatedSource.expand =
    locatedSource.expandLocated.map LocatedInstruction.instruction :=
  Source.expand_eq_map_located locatedSource
example : locatedSource.expandLocated.length = locatedSource.expand.length :=
  Source.expandLocated_length locatedSource
example : (locatedSource.locatedInstructionAt? 2).map
    LocatedInstruction.instruction = locatedSource.expand[2]? :=
  Source.instruction_of_locatedInstructionAt? locatedSource 2
example : (locatedSource.locatedInstructionAt? 3).isSome = false := by decide

example : (generator.generate 7).instructionCount = 1 := by
  simp [generator, VerifiedFragment.instructionCount, addFragment,
    Source.instructionCount]
example : (generator.generate 7).effects = effects.derive (generator.expand 7) :=
  Generator.generated_effects_exact generator 7
example : (generator.contract 7).WellFormed :=
  Generator.generated_contract_wellFormed generator 7
example : (generator.generate 7).instructionCount = (generator.expand 7).length :=
  Generator.generated_instructionCount generator 7

example : ClassifiesExactlyOneExit (contract 7) 7 := by
  apply (generator.generate 7).localCorrect 0 7 rfl
  simp [generator, addFragment, semantics, eval, evalInstruction]

example : ClassifiesExactlyOneExit (contract 7) 7 := by
  apply Generator.generated_execution_classified generator 7 rfl
  simp [generator, Generator.expand, addFragment, semantics, eval, evalInstruction]

def overlappingExits : BlockContract Nat where
  requires := fun _ => True
  exits := [
    ⟨exitTag "normal", fun _ => True⟩,
    ⟨exitTag "fault", fun _ => True⟩
  ]

example : ¬ ClassifiesExactlyOneExit overlappingExits 0 := by
  simp [ClassifiesExactlyOneExit, overlappingExits] <;> decide

example {candidate : ExitContract Nat}
    (classified : ClassifiesExactlyOneExit (contract 7) 7)
    (member : candidate ∈ (contract 7).exits)
    (holds : candidate.ensures 7) : candidate.tag = exitTag "normal" := by
  let normal : ExitContract Nat :=
    ⟨exitTag "normal", fun state => state = 7⟩
  have normalMember : normal ∈ (contract 7).exits := by
    simp [normal, contract]
  have normalHolds : normal.ensures 7 := by
    simp [normal]
  exact classified_exit_tags_equal classified member normalMember
    holds normalHolds

end Grass.Tests.Construct.Fragment
