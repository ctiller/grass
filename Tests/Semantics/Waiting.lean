import Grass.Semantics.Waiting
import Grass.Refinement.Console.WriteWaiting

/-! Negative waiting fixtures and the portable console consumer. -/
namespace Grass.Tests.Semantics.Waiting

open RelationalSystem

private def stuck : RelationalSystem Unit where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => False
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun impossible => False.elim impossible

private def permitsWait : WaitProtocol Unit where
  Response := fun _ => Unit
  Allowed := fun _ _ => True
  AllowsPermanentWait := fun _ => True

/-- Even permission to wait cannot turn ordinary internal deadlock into an
external frontier: an allowed response must actually be possible. This holds
for every attempted boundary interpretation, not just one with empty Pending. -/
theorem ordinary_deadlock_rejected (boundary : stuck.WaitBoundary permitsWait)
    (history : stuck.History) : ¬ Nonempty (PermanentWait boundary history) := by
  rintro ⟨waiting⟩
  obtain ⟨_, _, _, _, _, impossible⟩ := waiting.reply_possible () trivial
  exact impossible

/-- Constructor distinctions do not depend on the finite observation view. -/
theorem infinite_not_waiting {Event Request : Type} {system : RelationalSystem Event}
    {protocol : WaitProtocol Request} (boundary : system.WaitBoundary protocol)
    (history : system.History)
    (execution : system.InfiniteContinuation history.state history.graph history.path.events)
    (waiting : PermanentWait boundary history) :
    CompleteHistory.infinite (boundary := boundary) history execution ≠
      CompleteHistory.waiting history waiting := by
  intro equal
  cases equal

/-- A declared terminal initial configuration needs no synthetic transition. -/
def zero_step_terminal {Event Request : Type} {system : RelationalSystem Event}
    {protocol : WaitProtocol Request} (boundary : system.WaitBoundary protocol)
    (state : system.State) (graph : system.Graph) (initial : system.Initial state graph)
    (terminal : system.Terminal state graph) : CompleteHistory boundary :=
  .terminal (History.initial initial) terminal

open Std.Logical Std.Console Std.Console.WriteProcess
open Refinement.Console.WriteWaiting

/-- A protocol that forbids nonresponse cannot borrow the model's pending bag
as permission, even at the exact reachable first write. -/
theorem console_wait_requires_permission (payload : Vec Byte) :
    ¬ Nonempty (PermanentWait (boundary (payload := payload) (fun _ => False))
      (readyHistory payload)) := by
  apply PermanentWait.impossible_when_forbidden
  intro _ _ forbidden
  exact forbidden

/-- The carrier represents a permanent first-write wait for every nonempty
payload when that exact write is allowed to remain unanswered. -/
example (payload : Vec Byte) (nonempty : 0 < payload.length)
    (mayWait : Demand payload → Prop) (permitted : mayWait (.write (startCursor payload))) :
    CompleteHistory (boundary mayWait) := waitingAtWrite payload nonempty mayWait permitted

end Grass.Tests.Semantics.Waiting
