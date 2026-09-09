import Grass.Spec.Console
import Grass.Spec.Resource

namespace Grass.Tests.Console.Contract
open Grass.Console Grass.Specification Grass.Semantics

inductive Result where
  | success
  | failure

private def policy : ConsoleWriteOutcomePolicy Result :=
  ⟨.success, .failure, .failure, .failure⟩
private def resources := ConsoleResourceModel.singleLine
private def contract := Console.writeLineContract resources "Hello, World!" policy
private def spec := (SpecProcess.ofRelational contract).withLiveness
  (.terminatesUnder [.environmentResponsive])

example : MeetsAllSpecificationTheorems spec :=
  Console.writeLineContractCorrect resources "Hello, World!" policy

example : Console.ContractView spec.contract := by apply Console.writeLineView

example : spec.denotation = (SpecProcess.ofRelational contract).denotation := rfl

/-- Liveness adds a theorem row while preserving all unrestricted reporting waits. -/
example : (spec.denotation (LineRendering.mk TextEncoding.utf8 "\r\n") ()).Complete :=
  let request : LineRequest Result := ⟨"Hello, World!", policy⟩
  let selected := ObservedBehavior.fullCutFailure request (LineRendering.mk TextEncoding.utf8 "\r\n")
  .waiting (ObservedBehavior.reportingAt request (LineRendering.mk TextEncoding.utf8 "\r\n") selected)
    (ObservedBehavior.reportingWait request (LineRendering.mk TextEncoding.utf8 "\r\n") selected)

example (key : spec.authorRequirements.Key) :
    (spec.withLiveness (.terminatesUnder [])).authorRequirements.statement
      (spec.oldKey (.terminatesUnder []) key) = spec.authorRequirements.statement key :=
  spec.withLiveness_oldStatement _ key

end Grass.Tests.Console.Contract
