import Grass.Console.Timing

namespace Grass.Tests.Console.Timing

open Grass.Std.Logical Grass.Semantics Grass.RelationalSystem Grass.Console.Behavior

private def failedAt {payload : Vec Byte} (cut : OutputCut payload) :
    CompleteHistory (boundary payload) :=
  let history := pendingAt payload cut
  let finished := history.append (.snoc .nil
    (Grass.Console.Behavior.Choice.reply cut (.finish .writeFailed))
    (.terminal .writeFailed) (Grass.Console.Behavior.State.finished cut .writeFailed) ()
    (by exact ⟨pendingAt_state payload cut, trivial, rfl, rfl⟩))
  .terminal finished ⟨cut, .writeFailed, rfl, trivial⟩

example (payload : Vec Byte) :
    BoundaryResponsive (BoundaryTimingStrategy.responding (boundary payload)) :=
  Grass.Console.Timing.respondingResponsive payload

example (payload : Vec Byte) (history : (system payload).History) :
    Nonempty (BoundaryTimingStrategy.GeneratedComplete
      (BoundaryTimingStrategy.responding (boundary payload))) :=
  Grass.Console.Timing.respondingGeneratedNonempty history

/-- Even the unfavorable full-cut failure is retained by every strategy. -/
example (payload : Vec Byte) (strategy : BoundaryTimingStrategy (boundary payload)) :
    strategy.Compatible (failedAt (OutputCut.full payload)) := by
  trivial

/-- Unrestricted timing retains the actual full-cut permanent wait. -/
example (payload : Vec Byte) :
    (BoundaryTimingStrategy.unrestricted (boundary payload)).Compatible
      (.waiting (pendingAt payload (OutputCut.full payload))
        (permanentWaitAt payload (OutputCut.full payload))) := by
  trivial

/-- Responding timing excludes that same wait without deleting it from the base carrier. -/
example (payload : Vec Byte) :
    ¬ (BoundaryTimingStrategy.responding (boundary payload)).Compatible
      (.waiting (pendingAt payload (OutputCut.full payload))
        (permanentWaitAt payload (OutputCut.full payload))) := by
  simp [BoundaryTimingStrategy.Compatible, BoundaryTimingStrategy.responding]

/-- Every arbitrary partial-cut history has an exact terminal suffix witness. -/
example (payload : Vec Byte) (cut : OutputCut payload) :
    Nonempty (TerminalExtension (boundary payload) (pendingAt payload cut)) :=
  (Grass.Console.Timing.completionAdequate payload).complete (pendingAt payload cut)

end Grass.Tests.Console.Timing
