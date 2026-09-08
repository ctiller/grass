import Grass.CFG.Contract

/-!
# CFG block-contract lookup fixtures

The fixtures exercise positive and negative exit lookup and recover the exact
structural membership and identity carried by a successful result.
-/

namespace Grass.Tests.CFG.Contract

open Grass Grass.CFG

def exitTag (name : String) : ExitTag := ⟨⟨"test.contract", name⟩⟩

def normal : ExitContract Nat :=
  ⟨exitTag "normal", fun state => state = 0⟩

def failed : ExitContract Nat :=
  ⟨exitTag "failed", fun _ => True⟩

def contract : BlockContract Nat where
  requires := fun _ => True
  exits := [normal, failed]

example : contract.WellFormed := by decide
example : contract.findExit? (exitTag "normal") = some normal := by rfl
example : contract.findExit? (exitTag "missing") = none := by decide

example (exit : ExitContract Nat)
    (hfind : contract.findExit? (exitTag "normal") = some exit) :
    exit ∈ contract.exits ∧ exit.tag = exitTag "normal" :=
  contract.findExit?_sound (exitTag "normal") exit hfind

example (tag : ExitTag) :
    (contract.findExit? tag).isSome = true ↔
      contract.declaresExit tag = true :=
  contract.findExit?_isSome_iff_declaresExit tag

example : ∃ exit, contract.findExit? (exitTag "failed") = some exit :=
  contract.exitForTag (exitTag "failed") (by decide)

end Grass.Tests.CFG.Contract
