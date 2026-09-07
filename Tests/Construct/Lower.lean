import Grass.Construct.Lower
import Tests.Construct.SourceAst

/-!
# Checked lowering fixtures

The fixture supplies one exact verified fragment for each authored block and
pins the total flattened instruction sequence and one-for-one source map.
-/

namespace Grass.Tests.Construct.Lower

open Grass.CFG Grass.Construct.Fragment Grass.Construct.Source
open Grass.Tests.Construct.SourceAst

def semantics : Semantics Nat Nat where
  Executes := fun _ _ _ => False

def effects : EffectModel Nat Nat where
  derive := List.length

def verifiedFirst : VerifiedFragment semantics effects first.cfg.contract where
  source := first.body
  contractWellFormed := by
    simp [first, contract, BlockContract.WellFormed, BlockContract.wellFormed,
      BlockContract.exitTags]
  effects := 2
  effectsExact := by simp [first, effects]
  localCorrect := by intros; contradiction

def verifiedSecond : VerifiedFragment semantics effects second.cfg.contract where
  source := second.body
  contractWellFormed := by
    simp [second, contract, BlockContract.WellFormed, BlockContract.wellFormed,
      BlockContract.exitTags]
  effects := 3
  effectsExact := by simp [second, effects]
  localCorrect := by intros; contradiction

def checkedFirst : VerifiedBlock (Terminal := String) String semantics effects where
  authored := first
  fragment := verifiedFirst
  sourceExact := rfl

def checkedSecond : VerifiedBlock (Terminal := String) String semantics effects where
  authored := second
  fragment := verifiedSecond
  sourceExact := rfl

def verified : VerifiedAst semantics effects source where
  structural := by decide
  blocks := [checkedFirst, checkedSecond]
  blocksExact := rfl

example : verified.lower.graph = source.toGraph := rfl

example : verified.lower.items.map LoweredInstruction.instruction = [1, 2, 3, 4, 5] :=
  VerifiedAst.lower_instructions_exact verified

example : verified.lower.items.map (fun item => (item.block, item.origin)) = [
    (blockId "first", ⟨[fragmentId "pair"], [], 0⟩),
    (blockId "first", ⟨[fragmentId "pair"], [], 1⟩),
    (blockId "second", ⟨[], [0], 0⟩),
    (blockId "second", ⟨[], [1, 0], 0⟩),
    (blockId "second", ⟨[], [1, 0], 1⟩)
  ] := by decide

end Grass.Tests.Construct.Lower
