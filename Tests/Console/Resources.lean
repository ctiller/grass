import Grass.Console.Resources

namespace Grass.Tests.Console.Resources

open Grass.Resource
open Grass.ConsoleWriteResources

/-- Capturing the authored neutral resource preserves its exact value index. -/
def neutralSnapshot : ConsoleResourceSnapshot (inferInstance : ResourceModel ConsoleResourceModel)
    ConsoleResourceModel.singleLine :=
  captured ConsoleResourceModel.singleLine

/-- The neutral instance selects no resource axis. -/
theorem neutral_axes_empty : neutralSnapshot.selectedAxes = [] :=
  neutralSnapshot.selectedAxes_empty

/-- The resource value is an index on the captured snapshot type. -/
theorem neutral_snapshot_value_exact
    (snapshot : ConsoleResourceSnapshot (inferInstance : ResourceModel ConsoleResourceModel)
      ConsoleResourceModel.singleLine) :
    snapshot.selectedAxes = [] :=
  snapshot.selectedAxes_empty

/-- Explicit lawful dictionaries let this fixture test both snapshot indices
without introducing a global `Nat` resource-model instance. -/
@[instance_reducible] def countingModel : ResourceModel Nat := ResourceModel.mk Counting.algebra

def exclusiveAlgebra : ResourceAlgebra Nat where
  compatible := Exclusive.compatible
  combine := Exclusive.combine
  alternative := Exclusive.alternative
  zero := 0
  le := (· ≤ ·)
  laws := Exclusive.laws

@[instance_reducible] def exclusiveModel : ResourceModel Nat := ResourceModel.mk exclusiveAlgebra

def countingZero : ConsoleResourceSnapshot countingModel 0 := ⟨[], rfl⟩

/- Reusing a snapshot at a different resource value is rejected by its index. -/
/--
error: Type mismatch
  countingZero
has type
  ConsoleResourceSnapshot countingModel 0
but is expected to have type
  ConsoleResourceSnapshot countingModel 1
-/
#guard_msgs in
#check (countingZero : ConsoleResourceSnapshot countingModel 1)

/- Reusing a snapshot under a different lawful model dictionary is rejected. -/
/--
error: Type mismatch
  countingZero
has type
  ConsoleResourceSnapshot countingModel 0
but is expected to have type
  ConsoleResourceSnapshot exclusiveModel 0
-/
#guard_msgs in
#check (countingZero : ConsoleResourceSnapshot exclusiveModel 0)

/-- The same exact model and resource indices remain usable. -/
def countingZeroAgain : ConsoleResourceSnapshot countingModel 0 := countingZero

end Grass.Tests.Console.Resources
