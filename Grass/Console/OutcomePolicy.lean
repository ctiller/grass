/-!
# The authored outcome policy for a console write

A spike author names one public outcome per way a console write can end.
`Grass.Console.writeLineContract` places these values directly on the trace's
terminal event (see that module for why no exit status appears here); the
driver tier later projects them to a platform status number.
-/

namespace Grass

/-- The authored total policy for the four console terminal causes. -/
structure ConsoleWriteOutcomePolicy (Outcome : Type) where
  success : Outcome
  stdoutUnavailable : Outcome
  writeFailed : Outcome
  noProgress : Outcome

end Grass
