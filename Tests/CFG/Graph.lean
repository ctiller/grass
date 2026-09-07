import Grass.CFG.Graph

/-!
# CFG structural closure fixtures

Positive and negative examples for the C0 graph checker.  The negative cases
pin one rejected defect each so later broadening cannot silently admit an
unresolved target, duplicate label, undeclared exit, uncovered exit, or two
destinations for one exit.
-/

namespace Grass.Tests.CFG.Graph

open Grass Grass.CFG

def blockId (name : String) : BlockId := ⟨⟨"test.cfg", name⟩⟩
def exitTag (name : String) : ExitTag := ⟨⟨"test.cfg", name⟩⟩

example : LawfulBEq BlockId := inferInstance
example : LawfulBEq ExitTag := inferInstance

inductive Terminal where
  | returned
  | failed
deriving Repr, DecidableEq, BEq

def normal : ExitContract Nat := ⟨exitTag "normal", fun _ => True⟩
def failed : ExitContract Nat := ⟨exitTag "failed", fun _ => True⟩

def entryContract : BlockContract Nat where
  requires := fun state => state = 0
  exits := [normal, failed]

def returnContract : BlockContract Nat where
  requires := fun _ => True
  exits := [normal]

def entryBlock : Block Nat Terminal where
  id := blockId "entry"
  contract := entryContract
  outgoing := [
    ⟨exitTag "normal", .block (blockId "return")⟩,
    ⟨exitTag "failed", .terminal .failed⟩
  ]

def returnBlock : Block Nat Terminal where
  id := blockId "return"
  contract := returnContract
  outgoing := [⟨exitTag "normal", .terminal .returned⟩]

def good : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [entryBlock, returnBlock]

example : good.WellFormed := by decide

example : good.directTargets = [blockId "return"] := by decide

example : good.predecessors (blockId "return") = [blockId "entry"] := by decide

def missingTarget : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [{ entryBlock with outgoing := [
    ⟨exitTag "normal", .block (blockId "missing")⟩,
    ⟨exitTag "failed", .terminal .failed⟩
  ] }]

example : ¬ missingTarget.WellFormed := by decide
example : missingTarget.unresolvedTargets = [blockId "missing"] := by decide

def duplicateBlock : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [entryBlock, entryBlock, returnBlock]

example : ¬ duplicateBlock.WellFormed := by decide

def missingEntry : Graph Nat Terminal where
  entry := blockId "missing"
  blocks := [entryBlock, returnBlock]

example : ¬ missingEntry.WellFormed := by decide

def undeclaredExit : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [{ entryBlock with outgoing := [
    ⟨exitTag "unknown", .block (blockId "return")⟩,
    ⟨exitTag "failed", .terminal .failed⟩
  ] }, returnBlock]

example : ¬ undeclaredExit.WellFormed := by decide

def uncoveredExit : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [{ entryBlock with outgoing := [
    ⟨exitTag "normal", .block (blockId "return")⟩
  ] }, returnBlock]

example : ¬ uncoveredExit.WellFormed := by decide

def duplicateExitDestination : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [{ entryBlock with outgoing := [
    ⟨exitTag "normal", .block (blockId "return")⟩,
    ⟨exitTag "normal", .terminal .returned⟩,
    ⟨exitTag "failed", .terminal .failed⟩
  ] }, returnBlock]

example : ¬ duplicateExitDestination.WellFormed := by decide

def duplicateContractExit : Graph Nat Terminal where
  entry := blockId "entry"
  blocks := [{ entryBlock with contract := {
    requires := fun _ => True
    exits := [normal, normal]
  } }, returnBlock]

example : ¬ duplicateContractExit.WellFormed := by decide

end Grass.Tests.CFG.Graph
