import Grass.Console.ObservedBehavior

namespace Grass.Tests.Console.ObservedBehavior

open Grass.Specification Grass.Semantics Grass.Console Grass.RelationalSystem
open Grass.Console.ObservedBehavior

private def request : LineRequest Bool := ⟨"ok", ⟨true, false, false, false⟩⟩
private def rendering : LineRendering := ⟨TextEncoding.utf8, "\r\n"⟩
private def failed := fullCutFailure request rendering

example : failed.publicOutcome = false := rfl
example : (reportingAt request rendering failed).state = .reporting failed := rfl
example : Nonempty (PermanentWait (boundary request rendering)
    (reportingAt request rendering failed)) := ⟨reportingWait request rendering failed⟩
example : (system request rendering).Terminal (observe request rendering failed).state () :=
  observe_terminal request rendering failed
example : ∃ history : (Behavior.system (rendering.bytes request.line)).History,
    history.state = .finished failed.cut failed.cause ∧
      Behavior.FinishAllowed failed.cut failed.cause :=
  reporting_has_component_terminal request rendering failed

end Grass.Tests.Console.ObservedBehavior
