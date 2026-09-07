import Grass.Unsafe.Lower
import Tests.Construct.Lower

/-!
# Checked-lowering erasure fixtures

The authored two-block fixture pins exact raw writer input and empty-output
canonicalization.
-/

namespace Grass.Tests.Unsafe.Lower

open Grass.Construct.Source Grass.Unsafe
open Grass.Tests.Construct.Lower Grass.Tests.Construct.SourceAst

def raw : RawHierarchy Nat := RawHierarchy.ofVerifiedAst verified

example : raw.flatten = source.instructions :=
  RawHierarchy.flatten_ofVerifiedAst verified

example : raw.flatten = [1, 2, 3, 4, 5] := by native_decide

def emptyLowered : LoweredProgram Nat String Nat where
  graph := source.toGraph
  items := []

example : RawHierarchy.ofLowered emptyLowered = .empty := by rfl

end Grass.Tests.Unsafe.Lower
