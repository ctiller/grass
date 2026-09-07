import Grass.CFG.Call

/-!
# Abstract call-contract fixtures

The fixtures pin explicit normal/fault/unwind coverage and reject missing,
duplicate, reordered, and stack-incompatible call sites.
-/

namespace Grass.Tests.CFG.Call

open Grass Grass.CFG

def exitTag (name : String) : ExitTag := ⟨⟨"test.call", name⟩⟩
def blockId (name : String) : BlockId := ⟨⟨"test.call", name⟩⟩
def externalId (name : String) : ExternalCallId := ⟨⟨"test.call", name⟩⟩

inductive Terminal where
  | returned
  | failed
deriving Repr, DecidableEq

def callStack : StackShape := ⟨40, []⟩

def normal : CallOutcomeContract Nat :=
  ⟨exitTag "normal", .normal, fun state => state = 0, callStack⟩

def fault : CallOutcomeContract Nat :=
  ⟨exitTag "fault", .fault, fun state => state ≠ 0, callStack⟩

def unwind : CallOutcomeContract Nat :=
  ⟨exitTag "unwind", .unwind, fun _ => True, .empty⟩

def provider : CallContract Nat where
  requires := fun _ => True
  entryStack := callStack
  outcomes := [normal, fault, unwind]

example : provider.WellFormed := by decide
example : provider.toBlockContract.exitTags =
    [exitTag "normal", exitTag "fault", exitTag "unwind"] := by decide

example : provider.toBlockContract.WellFormed :=
  CallContract.toBlockContract_wellFormed provider (by decide)

def good : CallSite Nat Terminal where
  target := .external (externalId "provider")
  contract := provider
  actualEntryStack := callStack
  returns := [
    ⟨exitTag "normal", .block (blockId "continue")⟩,
    ⟨exitTag "fault", .terminal .failed⟩,
    ⟨exitTag "unwind", .terminal .failed⟩
  ]

example : good.WellFormed := by decide

def missingFault : CallSite Nat Terminal := {
  good with returns := [
    ⟨exitTag "normal", .block (blockId "continue")⟩,
    ⟨exitTag "unwind", .terminal .failed⟩
  ]
}
example : ¬ missingFault.WellFormed := by decide

def duplicateNormal : CallSite Nat Terminal := {
  good with returns := [
    ⟨exitTag "normal", .block (blockId "continue")⟩,
    ⟨exitTag "normal", .terminal .failed⟩,
    ⟨exitTag "fault", .terminal .failed⟩,
    ⟨exitTag "unwind", .terminal .failed⟩
  ]
}
example : ¬ duplicateNormal.WellFormed := by decide

def reordered : CallSite Nat Terminal := {
  good with returns := [
    ⟨exitTag "fault", .terminal .failed⟩,
    ⟨exitTag "normal", .block (blockId "continue")⟩,
    ⟨exitTag "unwind", .terminal .failed⟩
  ]
}
example : ¬ reordered.WellFormed := by decide

def incompatibleStack : CallSite Nat Terminal := {
  good with actualEntryStack := ⟨32, []⟩
}
example : ¬ incompatibleStack.WellFormed := by decide

def leakedScope : CallSite Nat Terminal := {
  good with actualEntryStack := ⟨40, [⟨⟨"test.call", "live"⟩⟩]⟩
}
example : ¬ leakedScope.WellFormed := by decide

def duplicateContract : CallContract Nat where
  requires := fun _ => True
  entryStack := callStack
  outcomes := [normal, normal]

example : ¬ duplicateContract.WellFormed := by decide

end Grass.Tests.CFG.Call
