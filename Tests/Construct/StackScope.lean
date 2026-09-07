import Grass.Construct.StackScope

/-!
# Exact lexical stack-scope closure fixtures

Fixtures cover exact all-exit closure and rejection of contract defects, exit
identity mismatch, escaping addresses, live loans, and live obligations.
-/

namespace Grass.Tests.Construct.StackScope

open Grass.Core Grass.CFG Grass.Construct Grass.Construct.Layout

private def tag (name : String) : ExitTag := ⟨⟨"test.stack.scope", name⟩⟩
private def normal : ExitTag := tag "normal"
private def fault : ExitTag := tag "fault"
private def contract : BlockContract Unit :=
  ⟨fun _ => True, [⟨normal, fun _ => True⟩, ⟨fault, fun _ => True⟩]⟩

private def closed : ScopeExit String := ⟨[], [], []⟩
private def validLedger : StackScopeLedger contract String :=
  ⟨[⟨normal, closed⟩, ⟨fault, closed⟩]⟩
private def checked : CheckedStackScope (contract := contract) (Resource := String) :=
  ⟨validLedger, by decide⟩

example : checked.ledger.exitTags = contract.exitTags := checked.exitTagsExact
example (exit : StackScopeExit String) (member : exit ∈ checked.ledger.exits) :
    exit.resources.WellFormed := checked.exitClosed exit member
example : (checkStackScope validLedger).isOk = true := by decide

private def mismatch : StackScopeLedger contract String :=
  ⟨[⟨fault, closed⟩, ⟨normal, closed⟩]⟩
example : (checkStackScope mismatch).map (fun _ => ()) =
    .error (.exitTagsMismatch [fault, normal] [normal, fault]) := by rfl

private def escaping : StackScopeLedger contract String :=
  ⟨[⟨normal, ⟨[⟨"address"⟩], [], []⟩⟩, ⟨fault, closed⟩]⟩
private def loaned : StackScopeLedger contract String :=
  ⟨[⟨normal, closed⟩, ⟨fault, ⟨[], ["loan"], []⟩⟩]⟩
private def obligated : StackScopeLedger contract String :=
  ⟨[⟨normal, closed⟩, ⟨fault, ⟨[], [], ["finalize"]⟩⟩]⟩

example : (checkStackScope escaping).map (fun _ => ()) = .error (.openExit normal) := by rfl
example : (checkStackScope loaned).map (fun _ => ()) = .error (.openExit fault) := by rfl
example : (checkStackScope obligated).map (fun _ => ()) = .error (.openExit fault) := by rfl

private def duplicateContract : BlockContract Unit :=
  ⟨fun _ => True, [⟨normal, fun _ => True⟩, ⟨normal, fun _ => True⟩]⟩
private def duplicateLedger : StackScopeLedger duplicateContract String :=
  ⟨[⟨normal, closed⟩, ⟨normal, closed⟩]⟩
example : (checkStackScope duplicateLedger).map (fun _ => ()) =
    .error .invalidContract := by rfl

end Grass.Tests.Construct.StackScope
