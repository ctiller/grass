import Grass.Std.Console.Process

/-! # Boundary cases for the portable write-all consumer

These fixtures exercise partitioned writes, failure after emission, and zero
progress. They do not certify a platform projection or a complete Hello run.
-/

namespace Tests.Std.ConsoleWrite

open Grass.Std.Logical Grass.Std.Console

private def payload : Vec Byte := ⟨[65, 66, 67]⟩
private def initial : WriteCursor payload := ⟨0, by decide⟩
private def one : WriteCount initial := ⟨1, by decide⟩
private def second : WriteCursor payload := advance initial one
private def two : WriteCount second := ⟨2, by decide⟩

example : respond initial (by decide) (.success one) = .retry second := rfl

example : respond second (by decide) (.success two) =
    .done .success (advance second two) := rfl

example : (WriteResponse.success one).emitted ++ (WriteResponse.success two).emitted =
    payload := by decide

example : (WriteResponse.success one).emitted ++ (WriteResponse.failure two).emitted =
    payload := by decide

example : respond second (by decide) (.failure two) =
    .done .writeFailed (advance second two) := rfl

example : (respond second (by decide) (.failure two)).cursor.committed = payload.length :=
  by decide

example : respond second (by decide) (.success ⟨0, by decide⟩) =
    .done .noProgress second := rfl

example : ¬ WriteProcess.Valid (.finished .success second) := by
  change ¬ (1 = 3)
  decide

example : ¬ (4 ≤ initial.remaining.length) := by decide

example : WriteProcess.decide (WriteProcess.State.writing
    (WriteProcess.startCursor Vec.empty)) = .terminal (.written .success
      (WriteProcess.startCursor Vec.empty)) := rfl

end Tests.Std.ConsoleWrite
