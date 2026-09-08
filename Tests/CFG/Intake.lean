import Grass.CFG.Intake

/-!
# Structural CFG intake fixtures

These fixtures bind opaque upstream entry and step identities to one closed
graph, then reject duplicate identities and missing block or edge targets.
-/

namespace Grass.Tests.CFG.Intake

open Grass Grass.CFG

def blockId (name : String) : BlockId := ⟨⟨"test.intake", name⟩⟩
def exitTag (name : String) : ExitTag := ⟨⟨"test.intake", name⟩⟩

inductive Terminal where
  | returned
deriving Repr, DecidableEq

inductive EntryId where
  | root
  | worker
deriving Repr, DecidableEq

inductive StepId where
  | dispatch
  | finish
deriving Repr, DecidableEq

def contract (tag : String) : BlockContract Nat where
  requires := fun _ => True
  exits := [⟨exitTag tag, fun _ => True⟩]

def graph : Graph Nat Terminal where
  entry := blockId "root"
  blocks := [
    ⟨blockId "root", contract "dispatch",
      [⟨exitTag "dispatch", .block (blockId "worker")⟩]⟩,
    ⟨blockId "worker", contract "finish",
      [⟨exitTag "finish", .terminal .returned⟩]⟩
  ]

def intake : AuthoredCFGIntake EntryId StepId graph where
  entries := [⟨.root, blockId "root"⟩, ⟨.worker, blockId "worker"⟩]
  steps := [
    ⟨.dispatch, ⟨blockId "root", exitTag "dispatch"⟩⟩,
    ⟨.finish, ⟨blockId "worker", exitTag "finish"⟩⟩
  ]

example : intake.WellFormed := by decide
example : graph.WellFormed := intake.graphWellFormed_of_wellFormed (by decide)
example : intake.entryIds.Nodup := intake.entryIdsNodup_of_wellFormed (by decide)
example : intake.stepIds.Nodup := intake.stepIdsNodup_of_wellFormed (by decide)

example : ∃ binding block,
    intake.findEntry? .root = some binding ∧
    graph.findBlock? binding.block = some block :=
  intake.blockForEntry (by decide) .root (by decide)

example : ∃ binding located,
    intake.findStep? .dispatch = some binding ∧
    graph.findEdge? binding.edge = some located :=
  intake.edgeForStep (by decide) .dispatch (by decide)

def duplicateEntry : AuthoredCFGIntake EntryId StepId graph := {
  intake with entries := [⟨.root, blockId "root"⟩, ⟨.root, blockId "worker"⟩]
}

example : ¬ duplicateEntry.WellFormed := by decide

def duplicateStep : AuthoredCFGIntake EntryId StepId graph := {
  intake with steps := [
    ⟨.dispatch, ⟨blockId "root", exitTag "dispatch"⟩⟩,
    ⟨.dispatch, ⟨blockId "worker", exitTag "finish"⟩⟩
  ]
}

example : ¬ duplicateStep.WellFormed := by decide

def missingBlock : AuthoredCFGIntake EntryId StepId graph := {
  intake with entries := [⟨.root, blockId "missing"⟩]
}

example : ¬ missingBlock.WellFormed := by decide

def missingEdge : AuthoredCFGIntake EntryId StepId graph := {
  intake with steps := [
    ⟨.dispatch, ⟨blockId "root", exitTag "missing"⟩⟩
  ]
}

example : ¬ missingEdge.WellFormed := by decide

end Grass.Tests.CFG.Intake
