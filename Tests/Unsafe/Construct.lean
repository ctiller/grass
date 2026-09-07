import Grass.Unsafe.Construct

/-!
# Unchecked construction fixtures

The malformed fixture remains representable for diagnostics while its taint
ledger is nonempty and no structural evidence is manufactured.
-/

namespace Grass.Tests.Unsafe.Construct

open Grass Grass.CFG Grass.Construct.Fragment Grass.Unsafe

private def blockId (name : String) : BlockId := ⟨⟨"test.unsafe", name⟩⟩
private def exitTag (name : String) : ExitTag := ⟨⟨"test.unsafe", name⟩⟩

private def contract : BlockContract Nat where
  requires := fun _ => True
  exits := [⟨exitTag "done", fun _ => True⟩]

private def malformedBlock : Grass.Construct.Source.Block Nat String Nat String :=
  uncheckedBlock
    ⟨blockId "missing-exit", contract, []⟩
    (.literal [1, 2])
    ["diagnostic-only"]

private def primary : Taint := ⟨.uncheckedConstruction, "exit is not connected"⟩
private def imported : Taint := ⟨.importedBytes, "origin is untrusted"⟩

private def raw : UncheckedAst Nat String Nat String :=
  uncheckedAst (blockId "missing-exit") [malformedBlock] primary

example : ¬raw.source.WellFormed := by native_decide
example : raw.taints = [primary] := rfl
example : raw.taints ≠ [] := raw.taints_ne_nil
example : (raw.addTaint imported).source = raw.source := rfl
example : (raw.addTaint imported).taints = [primary, imported] := rfl
example : raw.source.blocks.map (fun block => block.body.expand) = [[1, 2]] := rfl

end Grass.Tests.Unsafe.Construct
