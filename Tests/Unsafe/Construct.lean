import Grass.Unsafe.Construct

/-!
# Explicit raw-construction fixtures

Fixtures pin exact raw flattening and preservation of both taint ledgers across
hierarchical concatenation.
-/

namespace Grass.Tests.Unsafe.Construct

open Grass.Unsafe

def literalTaint : Taint := ⟨"fixture literal", .literal⟩
def importedTaint : Taint := ⟨"fixture import", .imported⟩

def left : RawConstruction Nat := .leaf literalTaint [1, 2]
def right : RawConstruction Nat := .leaf importedTaint [3]
def combined : RawConstruction Nat := left.append right

example : combined.erase.flatten = [1, 2, 3] := by rfl
example : combined.taints = [literalTaint, importedTaint] := by rfl
example : combined.taints ≠ [] := combined.tainted

end Grass.Tests.Unsafe.Construct
